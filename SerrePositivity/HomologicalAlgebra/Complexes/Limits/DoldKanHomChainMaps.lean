module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedHomChainMap

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {x' y' : E}

def homModuleChainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := R) x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := R) x' y' where
  app n := ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_pullback f α.unop.toOrderHom s

lemma pinchedLinearDataMap_signChange (f : homObject R D x y ⟶ homObject R E x' y')
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData s) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap f s) := by
  funext i
  change f.f i.val.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (i.val.1.card - 1) • s i) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (i.val.1.card - 1) • f.f i.val.2 (s i)
  exact map_zsmul _ _ _

def standardModuleChainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x' y' :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso (R := R) x y).inv ≫ _root_.SerrePositivity.ComplexLimits.homModuleChainMap f ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso (R := R) x' y').hom

lemma standardModuleChainMap_val (f : homObject R D x y ⟶ homObject R E x' y')
    (n : SimplexCategoryᵒᵖ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n.unop.len) :
    ((_root_.SerrePositivity.ComplexLimits.standardModuleChainMap f).app n s).val = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap f s.val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData s.val)) = _
  rw [← _root_.SerrePositivity.ComplexLimits.pinchedLinearDataMap_signChange, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_involutive]

lemma homSpaceLiftIso_chainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    SSet.uliftFunctor.{v, u}.map (Functor.whiskerRight (_root_.SerrePositivity.ComplexLimits.homModuleChainMap f)
      (forget (ModuleCat R))) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := R) x' y').hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := R) x y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x' y' n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f s.down).toPinched =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex f s.down.toPinched)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]

end SerrePositivity.ComplexLimits
