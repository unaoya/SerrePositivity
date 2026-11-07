module

public import SerrePositivity.HomologicalAlgebra.Cech.BaseChange
public import SerrePositivity.HomologicalAlgebra.Cech.Double
public import SerrePositivity.HomologicalAlgebra.Cech.Split

/-!
概要：環の射の Čech 完全性の比較と合成の消去（BM18 Lemma 3.4 の二重複体による議論）。
方針：二つの余脈体のテンソル積を取り、正次数の行・列での底変換の完全性から増大軸を比較する。
規約：合成の場合、C の各 Čech 項上では B からの射を使って切断を作る。
使われ方：構造層の arc 降下の証明と、v 降下の判定法。
-/

@[expose] public section
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicTopology TensorProduct
open scoped Simplicial

namespace SerrePositivity.Cech

set_option backward.isDefEq.respectTransparency false

variable {A : CommRingCat.{u}}

/-- 基底上のテンソル積を二変数関手として取る。 -/
def ringTensor (A : CommRingCat.{u}) : Under A × Under A ⥤ CommRingCat.{u} where
  obj P := CommRingCat.of (P.1 ⊗[A] P.2)
  map f := CommRingCat.ofHom
    (Algebra.TensorProduct.map (CommRingCat.toAlgHom f.1) (CommRingCat.toAlgHom f.2)).toRingHom
  map_id P := by
    rcases P with ⟨P, Q⟩
    simp only [prod_id, CommRingCat.toAlgHom_id, Algebra.TensorProduct.map_id]
    rfl
  map_comp {P Q R} f g := by
    rcases P with ⟨P₁, P₂⟩
    rcases Q with ⟨Q₁, Q₂⟩
    rcases R with ⟨R₁, R₂⟩
    simp only [prod_comp, CommRingCat.toAlgHom_comp, Algebra.TensorProduct.map_comp]
    rfl

/-- 基底環の下の圏に値を取る増大単体図式。 -/
abbrev asDiagram (B : Under A) : AugmentedSimplexCategory ⥤ Under A :=
  AugmentedSimplexCategory.equivAugmentedCosimplicialObject.inverse.obj (underCech B)

/-- 二つの増大 Čech 余脈体の項ごとのテンソル積。 -/
def tensorCech (B C : Under A) : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤
    CommRingCat.{u} :=
  (asDiagram B).prod (asDiagram C) ⋙ ringTensor A

/-- B の指定次数の項を基底として C の Čech 余脈体を底変換する。 -/
abbrev changeToTerm (B C : Under A) (i : ℕ) : Arrow CommRingCat.{u} :=
  let D := (asDiagram B).obj (simplex i)
  Arrow.mk ((CommRingCat.tensorProd A D.right).obj C).hom

/-- テンソル積の二つの因子の入れ替え。 -/
def tensorSwap (D : Under A) :
    (Functor.curryObj (ringTensor A)).flip.obj D ≅ (Functor.curryObj (ringTensor A)).obj D :=
  NatIso.ofComponents (fun B => (Algebra.TensorProduct.comm A B D).toRingEquiv.toCommRingCatIso) (by
    intro B C f
    apply CommRingCat.hom_ext
    apply RingHom.ext
    change ∀ x : B ⊗[A] D, _ = _
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b d => rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

/-- テンソル積の二重図式の列は、第一因子の項による底変換。 -/
def colTensorIso (B C : Under A) (i : ℕ) :
    col (tensorCech B C) i ≅ (changeToTerm B C i).augmentedCechConerve := by
  let D := (asDiagram B).obj (simplex i)
  let T := CommRingCat.tensorProd A D.right
  letI := tensorProd_preservesColimits A D.right
  let e := underCechMapIso T C
  have e' := (CosimplicialObject.Augmented.whiskeringObj _ _ (Under.forget D.right)).mapIso e
  let F :=
    (AugmentedSimplexCategory.equivAugmentedCosimplicialObject (C := CommRingCat.{u})).functor
  let U := Under.forget D.right
  let e₁ := (Functor.curryObjProdComp (asDiagram B) (asDiagram C) (ringTensor A)).app (simplex i)
  have e₁' : col (tensorCech B C) i ≅ F.obj (asDiagram C ⋙ T ⋙ U) := F.mapIso e₁
  have e₂ : F.obj (asDiagram C ⋙ T ⋙ U) ≅
      (CosimplicialObject.Augmented.whiskeringObj _ _ U).obj
        ((CosimplicialObject.Augmented.whiskeringObj _ _ T).obj (underCech C)) := by
    refine Comma.isoMk (Iso.refl _) (Iso.refl _) ?_
    apply NatTrans.ext
    funext n
    change 𝟙 _ ≫ U.map (𝟙 _ ≫ T.map ((underCech C).hom.app n)) =
      U.map (T.map ((underCech C).hom.app n)) ≫ 𝟙 _
    simp
  exact e₁' ≪≫ e₂ ≪≫ e'

/-- テンソル積の二重図式の行は、第二因子の項による底変換。 -/
def rowTensorIso (B C : Under A) (j : ℕ) :
    row (tensorCech B C) j ≅ (changeToTerm C B j).augmentedCechConerve := by
  let D := (asDiagram C).obj (simplex j)
  let F :=
    (AugmentedSimplexCategory.equivAugmentedCosimplicialObject (C := CommRingCat.{u})).functor
  let e₁ : (Functor.curryObj (tensorCech B C)).flip.obj (simplex j) ≅
      asDiagram B ⋙ (Functor.curryObj (ringTensor A)).flip.obj D :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro x y f
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      change (ringTensor A).map (Prod.mkHom ((asDiagram B).map f)
          ((asDiagram C).map (𝟙 (simplex j)))) =
        (ringTensor A).map (Prod.mkHom ((asDiagram B).map f) (𝟙 D))
      rw [(asDiagram C).map_id])
  let e₂ := Functor.isoWhiskerLeft (asDiagram B) (tensorSwap D)
  let e₃ := (Functor.curryObjProdComp (asDiagram C) (asDiagram B) (ringTensor A)).app (simplex j)
  exact F.mapIso (e₁ ≪≫ e₂ ≪≫ e₃.symm) ≪≫ colTensorIso C B j

private theorem col_acyclic_iff (B C : Under A) (i : ℕ) :
    (augmentedCochain.obj (col (tensorCech B C ⋙ ringToAb) i)).Acyclic ↔
      IsCechExact (changeToTerm B C i) := by
  exact (ringCechExact_iff_acyclic (col (tensorCech B C) i)).symm.trans
    (ringCechExact_iff_of_iso (colTensorIso B C i))

private theorem row_acyclic_iff (B C : Under A) (j : ℕ) :
    (augmentedCochain.obj (row (tensorCech B C ⋙ ringToAb) j)).Acyclic ↔
      IsCechExact (changeToTerm C B j) := by
  exact (ringCechExact_iff_acyclic (row (tensorCech B C) j)).symm.trans
    (ringCechExact_iff_of_iso (rowTensorIso B C j))

private theorem changeToTerm_zero_iff (B C : Under A) :
    IsCechExact (changeToTerm B C 0) ↔ IsCechExact (Arrow.mk C.hom) := by
  let D := (asDiagram B).obj (simplex 0)
  change IsCechExact (Arrow.mk ((CommRingCat.tensorProd A D.right).obj C).hom) ↔ _
  let : Module.FaithfullyFlat A D.right := by
    change Module.FaithfullyFlat A A
    infer_instance
  exact isCechExact_baseChange_iff D.right C

/-- 二重 Čech 複体の正次数の行と列が完全なら、二つの元の複体の完全性は同値。
（BM18 Lemma 3.4 の二重複体による比較） -/
theorem isCechExact_iff_of_tensorCech (B C : Under A)
    (hr : ∀ j, 0 < j → IsCechExact (changeToTerm C B j))
    (hc : ∀ i, 0 < i → IsCechExact (changeToTerm B C i)) :
    IsCechExact (Arrow.mk B.hom) ↔ IsCechExact (Arrow.mk C.hom) := by
  exact (changeToTerm_zero_iff C B).symm.trans <|
    (row_acyclic_iff B C 0).symm.trans <|
    (doubleCech_acyclic_iff (tensorCech B C ⋙ ringToAb)
      (fun j hj => (row_acyclic_iff B C j).mpr (hr j hj))
      (fun i hi => (col_acyclic_iff B C i).mpr (hc i hi))).trans <|
    (col_acyclic_iff B C 0).trans (changeToTerm_zero_iff B C)

/-- 基底への代数準同型があれば、底変換後の射には左逆があり、増大 Čech 複体は完全。 -/
theorem isCechExact_baseChange_of_map (B D : Under A) (f : B ⟶ D) :
    IsCechExact (Arrow.mk ((CommRingCat.tensorProd A D.right).obj B).hom) := by
  let a := CommRingCat.toAlgHom f
  let r := AlgHom.liftEquiv A D.right B D.right a
  apply isCechExact_of_retraction _ (CommRingCat.ofHom r.toRingHom)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact r.commutes

/-- 合成 A → B → C の完全性と B の正次数の各項上での合成の完全性から
A → B の完全性を得る（BM18 Lemma 3.4 の消去）。 -/
theorem isCechExact_of_comp (B C : Under A) (g : B ⟶ C)
    (hC : IsCechExact (Arrow.mk C.hom))
    (hc : ∀ i, 0 < i → IsCechExact (changeToTerm B C i)) :
    IsCechExact (Arrow.mk B.hom) := by
  apply (isCechExact_iff_of_tensorCech B C (fun j hj => ?_) hc).mpr hC
  cases j with
  | zero => omega
  | succ j =>
    exact isCechExact_baseChange_of_map B _ (g ≫ underCechInclusion C ⦋j⦌ 0)

end SerrePositivity.Cech
