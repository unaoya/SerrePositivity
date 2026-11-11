module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：h Fun の二胞体の成分評価と hX 上の自然変換の一致。
方針：辺代表に帰着し、評価の二つの定義とパラメータ前合成を照合する。
規約：標的だけを quasicategory とする。
使われ方：B2 の反射単位の局所性と同型不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：h Fun の二胞体の頂点評価は h 圏間の自然変換の成分。
方針：二胞体の辺代表を取り、積の評価と固定頂点評価を比較する。
規約：A の quasicategory 性は不要。使われ方：単位成分の自然性。 -/
lemma functorCellToNatTrans_app_eq_evaluate {A X : SSet.{u}} [Quasicategory X]
    {U V : A ⟶ X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorCellToNatTrans α).app (HomotopyCategory.mk x) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) α
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorCellToNatTrans, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate, NatTrans.comp_app, eqToHom_app,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  symm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex x U)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex x V)
    (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)))
    ((e.tensor (SSet.Truncated.Edge.id (X := (truncation 2).obj A) x)).map
      ((truncation 2).map ((β_ ((ihom A).obj X) A).hom ≫ (ihom.ev A).app X)))
  change e.edge.app (Opposite.op ⦋1⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
    e.edge.app (Opposite.op ⦋1⦌) (𝟙 _)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]

/-- 概要：固定頂点での評価はパラメータの前合成と厳密に可換。
方針：定値単体の像の自然性を使う。
規約：quasicategory 性は不要。使われ方：包含上の単位の成分の回収。 -/
lemma evaluateFunctorAt_precomp {A B X : SSet.{u}} (i : A ⟶ B) (x : A _⦋0⦌) :
    (pre i).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (i.app (Opposite.op ⦋0⦌) x) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change F.app (Opposite.op ⦋n⦌) (𝟙 _)
    (i.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
  rfl

/-- 概要：可逆な h Fun の二胞体の各点の成分は可逆。
方針：評価関手で同型を写し両端の輸送を合成する。
規約：始域・標的の quasicategory 性は不要。使われ方：反射像の局所性。 -/
instance functorHomEvaluate_isIso {A X : SSet.{u}} {U V : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) [IsIso α] (x : A _⦋0⦌) : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
  infer_instance

/-- 概要：二胞体の前合成を評価すると元の二胞体を像の頂点で評価したもの。
方針：単体的な評価の可換性を h に移し、端点の輸送を相殺する。
規約：標的だけを quasicategory とする。使われ方：包含上の可逆単位の成分。 -/
lemma functorHomEvaluate_precomp {A B X : SSet.{u}} {U V : B ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (i : A ⟶ B) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (U := i ≫ U) (V := i ≫ V)
      ((hoFunctor.map ((pre i).app X)).toFunctor.map α) x =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α (i.app (Opposite.op ⦋0⦌) x) := by
  have h := congrArg (fun k : (ihom B).obj X ⟶ X => (hoFunctor.map k).toFunctor)
    (evaluateFunctorAt_precomp (X := X) i x)
  simp only [Functor.map_comp] at h
  have hh := CategoryTheory.Functor.congr_hom h α
  change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.map
    ((hoFunctor.map ((pre i).app X)).toFunctor.map α) = _ at hh
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate]
  rw [hh]
  simp [Category.assoc]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
