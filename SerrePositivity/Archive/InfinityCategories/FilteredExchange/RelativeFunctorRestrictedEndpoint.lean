module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：底を固定した相対関手の終点評価と前合成の厳密な合成則。
方針：相対制限の合成を一つの制限へ戻し、同じ底の表示変更と引き戻しを保つ。
規約：指定終点の値を保持。使われ方：同じ第零面の三辺と全終点の指定比較の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の相対関手を指定部分で制限し、同じ指定底の引き戻しへ戻す。 -/
def relativeFunctorRestrictedEndpoint {A C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F)
    (hj : j ≫ b = a ≫ q) :
    relativeFunctorSpace p b ⟶ relativeFunctorSpace (pullback.snd p q) a :=
  relativeFunctorPre p b j ≫ eqToHom (congrArg (relativeFunctorSpace p) hj) ≫
    (relativeFunctorBaseChangeIso p q a).inv

/-- 元の同じ制限射の等式は、底の表示変更を含めた指定終点評価の等式を与える。 -/
lemma relativeFunctorRestrictedEndpoint_congr {A C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) {j j' : C ⟶ A} (q : F ⟶ B) (a : C ⟶ F)
    (h : j = j') (hj : j ≫ b = a ≫ q) (hj' : j' ≫ b = a ≫ q) :
    relativeFunctorRestrictedEndpoint p b j q a hj =
      relativeFunctorRestrictedEndpoint p b j' q a hj' := by
  subst j'
  rfl

/-- 同じ元の終点の評価は、部分図式への前合成と厳密に合成する。 -/
lemma relativeFunctorRestrictedEndpoint_pre {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (h : D ⟶ A) (j : C ⟶ D)
    (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ (h ≫ b) = a ≫ q) :
    relativeFunctorPre p b h ≫ relativeFunctorRestrictedEndpoint p (h ≫ b) j q a hj =
      relativeFunctorRestrictedEndpoint p b (j ≫ h) q a
        (by rw [Category.assoc]; exact hj) := by
  unfold relativeFunctorRestrictedEndpoint
  rw [← Category.assoc (relativeFunctorPre p b h), relativeFunctorPre_comp]

/-- 全延長の指定終点評価は、包含と同じ元の相対終点評価の厳密な合成。 -/
lemma relativeFunctorExtensionEndpoint_factor {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q) :
    relativeFunctorExtensionSpaceι p b i v hv ≫ relativeFunctorRestrictedEndpoint p b j q a hj =
      relativeFunctorExtensionEndpoint p b i v hv j q a hj := rfl

end SerrePositivity.InfinityCategories.F2
