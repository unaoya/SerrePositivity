module
public import SerrePositivity.KST.SConstruction.DGTensorLeftUnitElements
public import SerrePositivity.DifferentialGraded.Module.FreeHomNaturality

/-! # 対角双加群の単位挿入を chain map として固定する
概要：元の単位元の挿入を、次数ごとの式から chain map の逆単位へ接続する。
方針：自由単位挿入と元の coend 包含を合成し、抽象加群で逆律を照合する。
規約：検証上限を変えない。使われ方：元の左単位と結合の圏論的な照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 元の単位元を自由に挿入し、対角との coend へ送る chain map。 -/
def dgDiagonalUnitInsertion (M : RightModule A B) (b : B) :
    M.obj (op b) ⟶ BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b) :=
  freeUnitInsert A b (M.obj (op b)) ≫
    BalancedTensor.ι A B M ((Bimodule.diagonal A B).leftAt b) b

/-- 挿入 chain map は元の次数零の単位挿入を回収する。 -/
lemma dgDiagonalUnitInsertion_apply (M : RightModule A B) (b : B) (n : ℤ)
    (m : (M.obj (op b)).X n) :
    (dgDiagonalUnitInsertion A B M b).f n m =
      BalancedTensor.element A B M ((Bimodule.diagonal A B).leftAt b) b
        m (unitElement A b).val (add_zero n) := by
  change (BalancedTensor.ι A B M ((Bimodule.diagonal A B).leftAt b) b).f n
    ((freeUnitInsert A b (M.obj (op b))).f n m) = _
  rw [freeUnitInsert_apply]
  rfl

/-- 挿入を元の左単位で回収すると同じ加群の恒等 chain map となる。 -/
lemma dgDiagonalUnitInsertion_evaluation (M : RightModule A B) (b : B) :
    dgDiagonalUnitInsertion A B M b ≫ (BalancedTensor.leftUnitValueIso A B M b).hom =
      𝟙 (M.obj (op b)) := by
  apply chain_ext_apply
  intro n m
  have hc := chain_comp_apply (dgDiagonalUnitInsertion A B M b)
    (BalancedTensor.leftUnitValueIso A B M b).hom n m
  have he := dgComplexMap_apply_congr (BalancedTensor.leftUnitValueIso A B M b).hom n
    (dgDiagonalUnitInsertion_apply A B M b n m)
  exact hc.trans (he.trans ((dgTensorLeftUnit_hom_insert A B M b n m).trans
    (dgComplexMap_identity_apply (M.obj (op b)) n m).symm))

/-- 挿入 chain map は、元の左単位同型の逆射そのものである。 -/
lemma dgDiagonalUnitInsertion_eq_inv (M : RightModule A B) (b : B) :
    dgDiagonalUnitInsertion A B M b = (BalancedTensor.leftUnitValueIso A B M b).inv := by
  apply (cancel_mono (BalancedTensor.leftUnitValueIso A B M b).hom).1
  rw [dgDiagonalUnitInsertion_evaluation, Iso.inv_hom_id]

omit [Small.{u} B] in
/-- 自由単位挿入は、tensor の左因子を追加する結合同型と両立する。 -/
lemma dgFreeUnitInsert_tensor (b : B) (X Y : Complex A) :
    (X ◁ freeUnitInsert A b Y) ≫ (α_ X Y (b ⟶[Complex A] b)).inv =
      freeUnitInsert A b (X ⊗ Y) := by
  dsimp only [freeUnitInsert]
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right, whiskerLeft_rightUnitor_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- 包含射上の二つの経路は、同じ右逆の回収式で全体の三重経路を比較できる。 -/
lemma dgComplex_triple_generator_of_unit {V X Y Z : Complex A}
    (i : V ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X) (s : X ⟶ Z)
    (hp : i ≫ f ≫ g = i ≫ s) (hu : s ≫ h = 𝟙 X) :
    i ≫ f ≫ g ≫ h = i ≫ 𝟙 X := by
  have ht := congrArg (fun k => k ≫ h) hp
  simpa only [Category.assoc, hu] using ht

end SerrePositivity.KST.SConstruction
