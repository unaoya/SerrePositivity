module

public import SerrePositivity.InfinityCategories.DoldKanComparison.DoldKanIso
public import SerrePositivity.InfinityCategories.Derived.PinchedHomChainMap

/-!
# 元の線形 Hom 模型への鎖写像の全作用

概要：同じ Hom 鎖写像を N4 線形模型・標準模型・実 pinched Hom へ作用させる。
方針：元の線形成分の写像と符号変換の可換性を使う。
規約：元の面・退化・宇宙持ち上げと同じ射を保つ。
使われ方：実 Γ Hom 同型と dg nerve の同じ射の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve.PinchedHom DoldKanComparison
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {x' y' : E}

def homModuleChainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    homModule (R := R) x y ⟶ homModule (R := R) x' y' where
  app n := ModuleCat.ofHom (pinchedLinearSimplexMap f)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact pinchedLinearSimplexMap_pullback f α.unop.toOrderHom s

lemma pinchedLinearDataMap_signChange (f : homObject R D x y ⟶ homObject R E x' y')
    {n : ℕ} (s : LinearData R x y n) :
    pinchedLinearDataMap f (signChangeData s) = signChangeData (pinchedLinearDataMap f s) := by
  funext i
  change f.f i.val.2 (degreeSign (i.val.1.card - 1) • s i) =
    degreeSign (i.val.1.card - 1) • f.f i.val.2 (s i)
  exact map_zsmul _ _ _

def standardModuleChainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    standardModule (R := R) x y ⟶ standardModule (R := R) x' y' :=
  (standardModuleIso (R := R) x y).inv ≫ homModuleChainMap f ≫
    (standardModuleIso (R := R) x' y').hom

lemma standardModuleChainMap_val (f : homObject R D x y ⟶ homObject R E x' y')
    (n : SimplexCategoryᵒᵖ) (s : StandardSimplex R x y n.unop.len) :
    ((standardModuleChainMap f).app n s).val = pinchedLinearDataMap f s.val := by
  change signChangeData (pinchedLinearDataMap f (signChangeData s.val)) = _
  rw [← pinchedLinearDataMap_signChange, signChangeData_involutive]

lemma homSpaceLiftIso_chainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    SSet.uliftFunctor.{v, u}.map (Functor.whiskerRight (homModuleChainMap f)
      (forget (ModuleCat R))) ≫ (homSpaceLiftIso (R := R) x' y').hom =
    (homSpaceLiftIso (R := R) x y).hom ≫ pinchedHomChainMap f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply (linearEquiv x' y' n.unop.len).injective
  change toLinearSimplex (pinchedLinearSimplexMap f s.down).toPinched =
    toLinearSimplex (pinchedHomChainMapSimplex f s.down.toPinched)
  rw [pinchedHomChainMapSimplex_linear, LinearSimplex.toLinearSimplex_toPinched,
    LinearSimplex.toLinearSimplex_toPinched]

end SerrePositivity.EInfinity.ComplexLimits
