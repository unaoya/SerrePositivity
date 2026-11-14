module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-! # 実屋根 fiber の固定頂点輸送の台

概要：固定頂点の等式で fiber を輸送しても、元の全空間への射影は変わらない。
方針：指定等式を消去して恒等写像へ戻す。
規約：充填性や安定性は不要。使われ方：実屋根 fiber と pinched Hom の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 固定頂点の等式による fiber の輸送は、全空間への射影を保つ。 -/
lemma roofVertexFiberTransport_ι {E B : SSet.{u}} (p : E ⟶ B)
    {a b : B _⦋0⦌} (h : a = b) :
    (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
  subst h
  rfl

/-- 固定頂点を戻す逆輸送も、全空間への射影を保つ。 -/
lemma roofVertexFiberTransport_inv_ι {E B : SSet.{u}} (p : E ⟶ B)
    {a b : B _⦋0⦌} (h : a = b) :
    (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h)).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  subst h
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
