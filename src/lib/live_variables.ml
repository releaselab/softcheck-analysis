open Base
open Softcheck
open Scil
open Cfg

module Make
    (E : Expr.S)
    (N : Cfg_node.S with type expr = E.t)
    (Cfg : Flow_graph.FlowGraph with type block = N.t) (S : sig
      val free_variables : E.t -> Set.M(String).t
      val expr_of_var : string -> E.t
    end) =
struct
  module Solve (P : sig
    val graph : Cfg.t
  end) =
  struct
    module L = Lattices.Powerset.Make (String)

    let kill n =
      let open N in
      match n.stmt_s with
      | Cfg_call_var_assign (lv, _, _) | Cfg_var_assign (lv, _) ->
          S.free_variables (S.expr_of_var lv)
      | Cfg_call_assign (lv, _, _) | Cfg_assign (lv, _) -> S.free_variables lv
      | Cfg_return _ | Cfg_call _ | Cfg_guard _ | Cfg_var_decl _ ->
          Set.empty (module String)

    let gen n =
      let open N in
      match n.stmt_s with
      | Cfg_var_assign (_, e) | Cfg_assign (_, e) | Cfg_return e | Cfg_guard e
        ->
          S.free_variables e
      | Cfg_call_var_assign (_, e, args)
      | Cfg_call_assign (_, e, args)
      | Cfg_call (e, args) ->
          List.fold_left
            ~f:(fun acc e -> Set.union acc (S.free_variables e))
            ~init:(S.free_variables e) args
      | Cfg_var_decl _ -> Set.empty (module String)

    module F = struct
      type vertex = Cfg.Vertex.t
      type state = L.t

      let f _ b s =
        let b' = Cfg.get P.graph b in
        let g = gen b' in
        let k = kill b' in
        Set.union (Set.diff s k) g

      let initial_state = Set.empty (module String)
    end

    include Framework.Dataflow.Backward.Make_solution (L) (Cfg) (F) (P)
  end
end
