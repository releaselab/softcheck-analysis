open Base
open Softcheck
open Scil
open Cfg

module Make
    (E : Expr.S)
    (N : Cfg_node.S with type expr = E.t)
    (Cfg : Flow_graph.FlowGraph with type block = N.t)
    (S : sig
      include Reaching_definitions.Language_component

      val eval : (string -> Lattices.Taint.t) -> expr -> Lattices.Taint.t
    end
    with type vertex = Cfg.Vertex.t
     and type expr = N.expr) =
struct
  module RD_S = Reaching_definitions.Make (E) (N) (Cfg) (S)

  module Solve (P : sig
    val graph : Cfg.t
  end) =
  struct
    module RD = RD_S.Solve (P)

    let blocks =
      Hashtbl.fold
        ~f:(fun ~key:_ ~data acc -> Set.add acc data)
        (Cfg.get_blocks P.graph)
        ~init:(Set.empty (module N))

    let vars =
      Set.fold blocks
        ~init:(Set.empty (module String))
        ~f:(fun acc b -> Set.union acc (RD.Spec.free_variables b))

    module Var_tainting_lattice =
      Lattices.Map.Make
        (String)
        (struct
          let bottom_elems = vars
        end)
        (Lattices.Taint)

    module Definition_location = Reaching_definitions.Definition_location

    module Reaching_definitions_lattice =
      Lattices.Powerset.Make (Definition_location)

    module L =
      Lattices.Pair.Make (Reaching_definitions_lattice) (Var_tainting_lattice)

    let ta s n =
      let open N in
      match n.stmt_s with
      | Cfg_assign (lv, rv) when S.is_ident lv ->
          let eval_rv = S.eval s rv in
          [ (S.ident_of_expr lv, eval_rv) ]
      | Cfg_var_assign (lv, rv) -> [ (lv, S.eval s rv) ]
      | Cfg_call_var_assign (v, _, _) -> [ (v, Lattices.Taint.bottom) ]
      | Cfg_call_assign (v, _, _) when S.is_ident v ->
          [ (S.ident_of_expr v, Lattices.Taint.bottom) ]
      | Cfg_call_assign _ | Cfg_return _ | Cfg_assign _ | Cfg_call _
      | Cfg_guard _ | Cfg_var_decl _ ->
          []

    module F = struct
      type vertex = Cfg.Vertex.t
      type state = L.t

      let f _ b s =
        let b' = Cfg.get P.graph b in
        let g = RD.gen b' in
        let k = RD.kill blocks b' in

        let s1 = Set.union (Set.diff (L.fst s) k) g in
        let new_tv =
          ta
            (fun d -> Option.value_exn (Var_tainting_lattice.get (L.snd s) d))
            b'
        in
        let s2 =
          List.fold_left
            ~f:(fun m (i, eval) -> Var_tainting_lattice.set m i eval)
            ~init:(L.snd s) new_tv
        in
        L.of_pair (s1, s2)

      let initial_state = L.bottom
    end

    include Framework.Dataflow.Forward.Make_solution (L) (Cfg) (F) (P)
  end
end
