module
public import SerrePositivity.InfinityCategories.DGNerve.HomotopyCategory
public import SerrePositivity.InfinityCategories.DGNerve.Quasicategory
public import SerrePositivity.InfinityCategories.Core.HomotopyCategoryBridge
public import SerrePositivity.InfinityCategories.Core.TerminalTransport

/-! # H⁰ の同型から dg nerve の実頂点同型へ

概要：全 dg 自然なホモトピー商の同型を Core の path-h の頂点同型に移す。
方針：検証済みの H⁰ 比較の完全忠実性で二切断の同型を回収し、path 比較へ送る。
規約：二つのホモトピー圏を定義的に同一視しない。使われ方：Yoneda の本質的全射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- H⁰ の指定された同型から実 dg nerve の頂点同型を構成する。 -/
def dgVertexIsoOfH0 {x y : D}
    (e : (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x) ≅
      (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) y)) :
    VertexIso (X := dgNerve A D) (Simplex.vertex x) (Simplex.vertex y) := by
  let a : nerveHomotopyCategory A D := ⟨Simplex.vertex x⟩
  let b : nerveHomotopyCategory A D := ⟨Simplex.vertex y⟩
  let e' : a ≅ b := (toH0 A D).preimageIso e
  exact (edgeToPathHomotopyCategory (twoTruncation A D)).mapIso e'

end SerrePositivity.InfinityCategories
