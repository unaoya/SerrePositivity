module

public import SerrePositivity.KST.Spectra.RelativeHomotopyRlpLift
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead

/-!
概要：点つき Kan 射の π 同型に沿い、指定部分の全区間を保つホモトピーを反映する。
方針：写像 path の終点射へ相対持ち上げし、元の源への射影で戻す。
規約：元の基底の二変数射へのトレースを保持する。使われ方：交換区間の自然性の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra

/-- 元の両端を結ぶ実ホモトピーと、指定した downstairs 二次元射への相対トレース。 -/
structure RelativeHomotopyReflection {E B : PointedSimplicialSet.{u}} {A X : SSet.{u}}
    (q : E ⟶ B) (i : A ⟶ X) {f g : X ⟶ E.right}
    (H : SSet.Homotopy (f ≫ q.right) (g ≫ q.right))
    (V : SSet.Homotopy (i ≫ f) (i ≫ g)) where
  homotopy : SSet.Homotopy f g
  trace : X ⊗ (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath q).right
  zero : SSet.ι₀ ≫ trace = f ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit q).right
  one : SSet.ι₁ ≫ trace = g ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit q).right
  over : trace ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection q).right = H.h
  retraction : trace ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction q).right = homotopy.h
  relative : i ▷ (Δ[1] : SSet.{u}) ≫ trace = V.h ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit q).right

/-- π 同型の写像 path 分解へ持ち上げ、同じ基底トレースを保って元の比較を回収する。 -/
def RelativeHomotopyReflection.choose {E B : PointedSimplicialSet.{u}} {A X : SSet.{u}}
    [KanComplex E.right] [KanComplex B.right] (q : E ⟶ B)
    (hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism q.right) (i : A ⟶ X) [Mono i] {f g : X ⟶ E.right}
    (H : SSet.Homotopy (f ≫ q.right) (g ≫ q.right))
    (V : SSet.Homotopy (i ≫ f) (i ≫ g))
    (hv : V.h ≫ q.right = i ▷ (Δ[1] : SSet.{u}) ≫ H.h) :
    RelativeHomotopyReflection q i H V := by
  let U := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit q).right
  let p := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection q).right
  let r := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction q).right
  have hfac : U ≫ p = q.right := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_projection q)
  have hret : U ≫ r = 𝟙 E.right := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction q)
  let Hbase : SSet.Homotopy ((f ≫ U) ≫ p) ((g ≫ U) ≫ p) := {
    h := H.h
    h₀ := by rw [Category.assoc, hfac]; exact H.h₀
    h₁ := by rw [Category.assoc, hfac]; exact H.h₁
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }
  let Vup : SSet.Homotopy (i ≫ (f ≫ U)) (i ≫ (g ≫ U)) := {
    h := V.h ≫ U
    h₀ := by rw [← Category.assoc, V.h₀, Category.assoc]; rfl
    h₁ := by rw [← Category.assoc, V.h₁, Category.assoc]; rfl
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }
  have hV : Vup.h ≫ p = i ▷ (Δ[1] : SSet.{u}) ≫ Hbase.h := by
    change (V.h ≫ U) ≫ p = _
    rw [Category.assoc, hfac, hv]
  let L := RelativeHomotopyRlpLift.choose p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism q hq) i Hbase Vup hV
  let R : SSet.Homotopy f g := {
    h := L.homotopy.h ≫ r
    h₀ := by
      rw [← Category.assoc, L.homotopy.h₀, Category.assoc, hret, Category.comp_id]
      rfl
    h₁ := by
      rw [← Category.assoc, L.homotopy.h₁, Category.assoc, hret, Category.comp_id]
      rfl
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }
  exact ⟨R, L.homotopy.h, L.homotopy.h₀, L.homotopy.h₁, L.over, rfl, L.relative⟩

/-- 回収された元の実ホモトピーも、指定部分の元の全区間そのものを保持する。 -/
lemma RelativeHomotopyReflection.homotopy_relative
    {E B : PointedSimplicialSet.{u}} {A X : SSet.{u}} {q : E ⟶ B} {i : A ⟶ X}
    {f g : X ⟶ E.right} {H : SSet.Homotopy (f ≫ q.right) (g ≫ q.right)}
    {V : SSet.Homotopy (i ≫ f) (i ≫ g)} (L : RelativeHomotopyReflection q i H V) :
    i ▷ (Δ[1] : SSet.{u}) ≫ L.homotopy.h = V.h := by
  rw [← L.retraction, ← Category.assoc, L.relative, Category.assoc,
    ← Under.comp_right, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction, Under.id_right, Category.comp_id]

end SerrePositivity.KST.Spectra
