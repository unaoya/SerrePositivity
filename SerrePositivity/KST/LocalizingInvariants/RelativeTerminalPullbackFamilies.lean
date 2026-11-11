module

public import SerrePositivity.KST.LocalizingInvariants.PullbackDiagramFamilies
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SimplexTerminalCoconeExtension
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration

/-!
概要：終端の列四角形と指定部分族を同時に固定して、前段の実 pullback 族を延長する。
方針：元の pullback 射影と終端包含の相対内部 Hom の全単射 RLP を使う。
規約：部分族・全 cospan・終端全四角形を同じ延長の厳密等式として保持する。
使われ方：境界輸送円柱の両端の既存族を保つ同時分母精密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 同じ pullback 射影と終端制限を同時に記憶する実 corner。 -/
def terminalPullbackFamilyCorner (X : SSet.{u}) (n : ℕ) :
    internalHom.PullbackObjObj (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint.{u} n) (pullbackProjection X) :=
  Functor.PullbackObjObj.ofHasPullback internalHom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (pullbackProjection X)

instance terminalPullbackFamilyCorner_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (terminalPullbackFamilyCorner X n).π :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ _ _ _

/-- 元の部分族・全 cospan・終端四角形の全族を厳密に保つ一つの相対延長。 -/
lemma exists_relative_terminalPullbackFamily {S P X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (n : ℕ) (j : S ⟶ P) [Mono j]
    (a : S ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (b : P ⟶ (ihom (Δ[n] : SSet.{u})).obj ((ihom (horn 2 2 : SSet.{u})).obj X))
    (c : P ⟶ (ihom (Δ[0] : SSet.{u})).obj (pullbackDiagrams X))
    (hab : a ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) = j ≫ b)
    (hac : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) = j ≫ c)
    (hbc : c ≫ (ihom (Δ[0] : SSet.{u})).map (pullbackProjection X) =
      b ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app ((ihom (horn 2 2 : SSet.{u})).obj X)) :
    ∃ F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X),
      j ≫ F = a ∧ F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) = b ∧
      F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) = c := by
  let sq := terminalPullbackFamilyCorner X n
  let t : P ⟶ sq.pt := sq.isPullback.lift c b hbc
  have ht₁ : t ≫ sq.fst = c := sq.isPullback.lift_fst _ _ _
  have ht₂ : t ≫ sq.snd = b := sq.isPullback.lift_snd _ _ _
  have ha : a ≫ sq.π = j ≫ t := by
    apply sq.hom_ext
    · rw [Category.assoc, sq.π_fst, Category.assoc, ht₁]
      exact hac
    · rw [Category.assoc, sq.π_snd, Category.assoc, ht₂]
      exact hab
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := sq.π) j inferInstance
  let w : CommSq a j sq.π t := ⟨ha⟩
  refine ⟨w.lift, w.fac_left, ?_, ?_⟩
  · have he := congrArg (fun f => f ≫ sq.snd) w.fac_right
    rw [Category.assoc, sq.π_snd, ht₂] at he
    exact he
  · have he := congrArg (fun f => f ≫ sq.fst) w.fac_right
    rw [Category.assoc, sq.π_fst, ht₁] at he
    exact he

end SerrePositivity.KST.LocalizingInvariants
