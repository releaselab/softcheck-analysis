open Base
open Softcheck
open Scil
open Cfg

module Definition_location = struct
  module T = struct
    type t = string * Label.t option [@@deriving eq, ord, sexp]

    let to_string (v, n) =
      let location_to_string = function
        | None -> "?"
        | Some l -> Int.to_string l
      in
      [%string "(%{v},%{location_to_string n})"]
  end

  include T
  include Comparable.Make (T)
end

module type Language_component = sig
  type vertex = int

  type definition_location = Definition_location.t

  type expr

  val is_ident : expr -> bool

  val ident_of_expr : expr -> string

  val free_variables : expr -> Set.M(String).t
end

module Make
    (E : Expr.S)
    (N : Cfg_node.S with type expr = E.t)
    (Cfg : Flow_graph.FlowGraph with type block = N.t)
    (S : Language_component with type vertex = Cfg.Vertex.t and type expr = E.t) =
struct
  module Solve (P : sig
    val graph : Cfg.t
  end) =
  struct
    let blocks =
      Hashtbl.fold
        ~f:(fun ~key:_ ~data:d acc -> Set.add acc d)
        (Cfg.get_blocks P.graph)
        ~init:(Set.empty (module N))

    module L = Lattices.Powerset.Make (Definition_location)
    module Spec = Node_specifics.Make (E) (N)

    let kill blocks n =
      let open N in
      match n.stmt_s with
      | Cfg_assign (lv, _) when S.is_ident lv ->
          let lv' = S.ident_of_expr lv in
          Set.add
            (Set.fold
               ~f:(fun acc l -> Set.add acc (lv', Some l.stmt_label))
               (Set.filter blocks ~f:(Spec.is_assignment ~var:lv))
               ~init:(Set.empty (module Definition_location)))
            (lv', None)
      | Cfg_assign _ | Cfg_call _ | Cfg_guard _ | Cfg_jump | Cfg_var_decl _ ->
          Set.empty (module Definition_location)

    let gen n =
      let open N in
      match n.stmt_s with
      | Cfg_assign (lv, _) when S.is_ident lv ->
          let lv' = S.ident_of_expr lv in
          Set.singleton (module Definition_location) (lv', Some n.stmt_label)
      | Cfg_assign _ | Cfg_call _ | Cfg_guard _ | Cfg_jump | Cfg_var_decl _ ->
          Set.empty (module Definition_location)

    module F = struct
      type vertex = Cfg.Vertex.t

      type state = L.t

      let f _ b s =
        let b' = Cfg.get P.graph b in
        let g = gen b' in
        let k = kill blocks b' in
        Set.union (Set.diff s k) g

      let initial_state =
        Set.fold
          ~f:(fun acc x ->
            let fv = Spec.free_variables S.free_variables x in
            Set.fold fv ~init:acc ~f:(fun acc x -> Set.add acc (x, None)))
          blocks
          ~init:(Set.empty (module Definition_location))
    end

    module Fix =
      Framework.Solvers.Make_fix (Cfg) (L) (F)
        (Framework.Dependencies.Forward (Cfg))

    let solution = Fix.solve P.graph

    let get_entry_result l = solution (Fix.Circ l)

    let get_exit_result l = solution (Fix.Bullet l)

    let result_to_string = L.to_string
  end
end
