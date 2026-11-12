module
public import SerrePositivity.KST.ProExcision.Lemma416Homotopy

/-!
# 同変な実ホモトピーの前合成と連結

概要：実 m 次ホモトピーの前合成・連結および A.6 の前合成は外部作用と可換。
方針：テンソルの合成則と区間射の加減法による同変性を使う。
規約：KST A.5・A.6・Lemma 4.16、非被約 C(H) の augmentation 補正。
使われ方：実帰納ホモトピーの各操作に行列同変性を付ける。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open scoped Simplicial
variable {G : SimplicialObject MonCat.{u}} {X Y Z : SSet.{u}}
variable {A : SimplicialSetAction G X} {B : SimplicialSetAction G Y} {C : SimplicialSetAction G Z}

/-- 概要：同変な幾何的写像による実ホモトピーの前合成は同変。
方針：二つのテンソル写像の合成則と入力の同変性を使う。
規約：KST A.6・4.16。使われ方：ψ を前合成した共役比較。 -/
lemma LinearizedMHomotopy.precomp_equivariant
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Z} {m : ℕ}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m) (p : X ⟶ Y)
    (hp : LinearizedEquivariant A B (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p))
    (hh : LinearizedCylinderEquivariant B C H.h) :
    LinearizedCylinderEquivariant A C (H.precomp p).h := by
  intro n a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (linearizedSetAction A n a) (𝟙 _) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p).app n) (𝟙 _) ≫ H.h.app n) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p).app n) (𝟙 _) ≫ H.h.app n) ≫ linearizedSetAction C n a
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, hp n a]
  simp only [Category.id_comp]
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p).app n) (linearizedSetAction B n a)
    (𝟙 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).obj n)) (𝟙 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).obj n))
  simp only [Category.id_comp] at ht
  erw [ht]
  simp only [Category.id_comp, Category.assoc]
  rw [hh n a]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (precomp_equivariant)

/-- 概要：同変な二つの実 m 次ホモトピーの連結は同変。
方針：同変な二つの区間射の和から中間射の同変な定数区間を引く。
規約：KST A.5・A.6・4.16、実連結は線形な加減法。
使われ方：共役比較と μ 版 A.5 の同変な連結。 -/
lemma LinearizedMHomotopy.trans_equivariant
    {f g k : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y} {m : ℕ}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m) (K : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy g k m)
    (hh : LinearizedCylinderEquivariant A B H.h) (hk : LinearizedCylinderEquivariant A B K.h)
    (hg : LinearizedEquivariant A B g) :
    LinearizedCylinderEquivariant A B (H.trans K).h :=
  (hh.add hk).sub hg.constant

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (trans_equivariant)

/-- 概要：準同型を前合成した A.6 の共役比較は外部作用に同変。
方針：u の固定性による A.6 の同変性を同変な f で引き戻す。
規約：KST 4.16、外部 G は一般のモノイド。
使われ方：行列作用で固定される実補助元 u による比較。 -/
lemma groupConjugationMHomotopy_equivariant {G T H : Type u} [Monoid G] [Group T] [Group H]
    (ρT : G →* Monoid.End T) (ρH : G →* Monoid.End H) (f : T →* H)
    (hf : ∀ a t, f (ρT a t) = ρH a (f t)) (u : H) (hu : ∀ a, ρH a u = u) (m : ℕ) :
    LinearizedCylinderEquivariant (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
      (discreteNerveAction (MonCat.of G) (MonCat.of H) ρH) (groupConjugationMHomotopy f u m).h :=
  ((conjugationLinearizedHomotopy u).truncate m).precomp_equivariant
    (nerveMap (SingleObj.mapHom _ _ f)) (groupLinearizedMap_equivariant ρT ρH f hf)
      (conjugationLinearizedHomotopy_equivariant ρH u hu)

end SerrePositivity.KST.ProExcision
