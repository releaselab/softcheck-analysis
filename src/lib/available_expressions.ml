open Base
open Softcheck
open Cfg
open Scil

module Make
    (E : Expr.S)
    (N : Cfg_node.S with type expr = E.t)
    (Cfg : Flow_graph.FlowGraph with type block = N.t) (S : sig
      val uses_lv_expr : N.expr -> N.expr -> bool
      val uses_var : string -> N.expr -> bool
      val aexp : E.t -> Set.M(E).t
      val free_variables : E.t -> Set.M(String).t
    end) =
struct
  module Solve (P : sig
    val graph : Cfg.t
  end) =
  struct
    module Spec =
      Node_specifics.Make (E) (N)
        (struct
          type expr = E.t

          let free_variables_expr = S.free_variables
        end)

    let aexp_star =
      let blocks =
        Hashtbl.fold
          ~f:(fun ~key:_ ~data:b acc -> Set.add acc b)
          (Cfg.get_blocks P.graph)
          ~init:(Set.empty (module N))
      in
      Set.fold
        ~f:(fun acc b ->
          Set.union (Spec.aexp ~get_non_trivial_subexpr:S.aexp b) acc)
        blocks
        ~init:(Set.empty (module E))

    module L =
      Lattices.Powerset.Make_reverse
        (struct
          include E
        end)
        (struct
          let bottom = aexp_star
        end)

    let kill aexp_star n =
      let open N in
      match n.stmt_s with
      | Cfg_call_var_assign (lv, _, _) | Cfg_var_assign (lv, _) ->
          Set.filter ~f:(S.uses_var lv) aexp_star
      | Cfg_call_assign (lv, _, _) | Cfg_assign (lv, _) ->
          Set.filter ~f:(S.uses_lv_expr lv) aexp_star
      | Cfg_return _ | Cfg_call _ | Cfg_guard _ | Cfg_var_decl _ ->
          Set.empty (module E)

    let gen n =
      let open N in
      match n.stmt_s with
      | Cfg_call_var_assign (lv, _, _) | Cfg_var_assign (lv, _) ->
          Set.filter
            ~f:(fun e -> not (S.uses_var lv e))
            (Spec.aexp ~get_non_trivial_subexpr:S.aexp n)
      | Cfg_call_assign (lv, _, _) | Cfg_assign (lv, _) ->
          Set.filter
            ~f:(fun e -> not (S.uses_lv_expr lv e))
            (Spec.aexp ~get_non_trivial_subexpr:S.aexp n)
      | Cfg_return _ | Cfg_call _ | Cfg_guard _ | Cfg_var_decl _ ->
          Spec.aexp ~get_non_trivial_subexpr:S.aexp n

    module F = struct
      type vertex = Cfg.Vertex.t
      type state = L.t

      let f _ b s =
        let b' = Cfg.get P.graph b in
        let g = gen b' in
        let k = kill aexp_star b' in
        Set.union (Set.diff s k) g

      let initial_state = Set.empty (module L.Elt)
    end

    include Framework.Dataflow.Forward.Make_solution (L) (Cfg) (F) (P)
  end
end
