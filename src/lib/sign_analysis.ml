open Base
open Softcheck
open Scil
open Cfg

module Make
    (E : Expr.S)
    (N : Cfg_node.S with type expr = E.t)
    (Cfg : Flow_graph.FlowGraph with type block = N.t) (S : sig
      val is_ident : E.t -> bool

      val ident_of_expr : E.t -> string

      val expr_sign_eval : (string -> Lattices.Sign.t) -> E.t -> Lattices.Sign.t
    end) =
struct
  module Solve (P : sig
    val graph : Cfg.t
  end) =
  struct
    let declaredVars = Set.empty (module String)
    (*let aux ((funcs, global_vars) : Cfg.program) =
      let ht = Hashtbl.create 10 in
      let () = List.iter (fun (f, vars, _) ->
        List.fold_left (fun acc v -> Set.add v acc) Set.empty vars |>
        Hashtbl.add ht f) funcs in
      ht in
      aux P.p*)

    module L =
      Lattices.Map.Make
        (String)
        (struct
          let bottom_elems = declaredVars
        end)
        (Lattices.Sign)

    let sign_eval env n =
      let f x = Option.value_exn (L.get env x) in
      let open N in
      match n.stmt_s with
      | Cfg_assign (lv, rv) when S.is_ident lv ->
          [ (S.ident_of_expr lv, S.expr_sign_eval f rv) ]
      | Cfg_var_decl v -> [ (v, Lattices.Sign.bottom) ]
      | Cfg_assign _ | Cfg_guard _ | Cfg_jump | Cfg_call _ -> []

    module F = struct
      type vertex = Cfg.Vertex.t

      type state = L.t

      let f _ b s =
        let b' = Cfg.get P.graph b in
        let evals = sign_eval s b' in
        List.fold_left ~f:(fun m (i, eval) -> L.set m i eval) ~init:s evals

      let initial_state = L.bottom
    end

    include Framework.Dataflow.Forward.Make_solution (L) (Cfg) (F) (P)
  end
end
