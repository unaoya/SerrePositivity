module


public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeComposition

/-!
概要：テンソルの二重 curry と、同じパラメータ内部 Hom の交換の整合性を厳密に示す。
方針：両辺を三度評価し、同じテンソル交換と元の評価射へ戻して照合する。
規約：閉対称モノイダル圏の全単体の等式。使われ方：混合源の標準全族作用の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

omit [SymmetricCategory C] in
/-- 同じテンソル curry を二度評価すると、元の結合子と評価そのものへ戻る。 -/
lemma InternalHomTensor.uncurry_uncurry_hom (A B Z : C) :
    uncurry (uncurry (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z).hom) =
      (α_ A B ((ihom (A ⊗ B)).obj Z)).inv ≫ (ihom.ev (A ⊗ B)).app Z := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.hom_eq, uncurry_curry, uncurry_curry]

/-- 同じ交換同型への任意の入力族を二度評価した、元の族と交換の厳密な式。 -/
lemma InternalHomExchange.uncurry_uncurry_pre (A K Z T : C)
    (r : T ⟶ (ihom A).obj ((ihom K).obj Z)) :
    uncurry (uncurry (r ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Z).hom)) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K T).hom ≫ K ◁ uncurry r ≫ (ihom.ev K).app Z := by
  rw [uncurry_natural_left, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc, ← whiskerLeft_comp_assoc, ← uncurry_eq r]

omit [MonoidalClosed C] in
/-- 二因子全体をパラメータと交換することは、同じ二因子を順に交換することに一致。 -/
lemma HomTensorStrength.exchange_tensor_block (A B P T : C) :
    (α_ A B (P ⊗ T)).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange (A ⊗ B) P T).hom =
      A ◁ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange B P T).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A P (B ⊗ T)).hom ≫ P ◁ (α_ A B T).inv := by
  apply (cancel_epi (A ◁ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange P B T).hom)).mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_tensor_left_reordered, ← whiskerLeft_comp_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_involution, whiskerLeft_id, Category.id_comp]

/-- 同じパラメータを二重 curry の外へ移す二つの操作は、射全体で厳密に一致する。 -/
lemma InternalHomExchange.tensor_curry (A B P Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (A ⊗ B) P Z).hom ≫
        (ihom P).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B ((ihom P).obj Z)).hom ≫
        (ihom B).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A P Z).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B P ((ihom A).obj Z)).hom := by
  apply uncurry_injective
  apply uncurry_injective
  apply uncurry_injective
  conv_lhs =>
    rw [uncurry_natural_right, uncurry_natural_left, uncurry_natural_left,
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.uncurry_uncurry_hom, associator_inv_naturality_right_assoc,
      ← uncurry_eq (uncurry (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (A ⊗ B) P Z).hom),
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom]
  conv_rhs =>
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_pre, uncurry_natural_right,
      whiskerLeft_comp, Category.assoc, ← uncurry_eq (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A P Z).hom,
      uncurry_natural_left, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc, ← whiskerLeft_comp_assoc,
      ← uncurry_eq (uncurry (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B ((ihom P).obj Z)).hom),
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.uncurry_uncurry_hom, whiskerLeft_comp]
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.HomTensorStrength.exchange_tensor_block A B P ((ihom (A ⊗ B)).obj ((ihom P).obj Z))
  have hc := congrArg (fun m => m ≫ P ◁ (ihom.ev (A ⊗ B)).app ((ihom P).obj Z) ≫
    (ihom.ev P).app Z) h
  simpa only [Category.assoc] using hc

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
