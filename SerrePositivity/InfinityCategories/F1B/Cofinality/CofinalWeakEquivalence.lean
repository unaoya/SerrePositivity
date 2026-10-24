module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalProductTest
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakMappingSpaces
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：左右 cofinal な射は弱ホモトピー同値。
方針：Kan 複体 Z と底の積の射影を検査し、相対関手空間の同型で通常の前合成へ移す。
規約：元の射の始域・終域に quasicategory 性や Kan 性を課さない。
使われ方：Kerodon Proposition 7.2.1.5(1)、Quillen A の必要性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：積の射影への相対制限の同値性から通常の写像空間の同値性を得る。
方針：指定底図式に対する検査同型の自然性と同値の消去を使う。
規約：Z は Kan 複体、a と i は任意。
使われ方：左右 cofinality のいずれの検査にも共通する橋。 -/
lemma cofinalProductTest_pre_isSimplicialHomotopyEquivalence
    {A D B : SSet.{u}} (a : A ⟶ B) (i : D ⟶ A) (Z : SSet.{u}) [KanComplex Z]
    (hi : IsSimplicialHomotopyEquivalence (cofinalFunctorPre (snd Z B) a i)) :
    IsSimplicialHomotopyEquivalence ((pre i).app Z) := by
  have h := hi.isQCatEquivalence.comp
    (qCatEquivalenceOfIso (cofinalProductTestIso (i ≫ a) Z)).isQCatEquivalence
  change IsQCatEquivalence
    (cofinalFunctorPre (snd Z B) a i ≫ (cofinalProductTestIso (i ≫ a) Z).hom) at h
  rw [cofinalProductTestIso_pre] at h
  have h₀ : IsQCatEquivalence (cofinalProductTestIso a Z).hom :=
    (qCatEquivalenceOfIso (cofinalProductTestIso a Z)).isQCatEquivalence
  exact (h₀.cancel_left h).isSimplicialHomotopyEquivalence

/-- 概要：left cofinal な任意の射は弱ホモトピー同値。
方針：全 Kan 標的 Z について、left fibration Z×B→B を検査する。
規約：始域・終域は任意の単体集合。
使われ方：Kerodon Proposition 7.2.1.5(1)。 -/
lemma IsLeftCofinal.isWeakHomotopyEquivalence {A B : SSet.{u}} {i : A ⟶ B}
    (hi : IsLeftCofinal i) : IsWeakHomotopyEquivalence i := by
  intro Z hZ
  exact (cofinalProductTest_pre_isSimplicialHomotopyEquivalence (𝟙 B) i Z
    (hi (Z ⊗ B) (snd Z B))).mapPiZero_bijective

/-- 概要：right cofinal な任意の射は弱ホモトピー同値。
方針：全 Kan 標的 Z について、right fibration Z×B→B を検査する。
規約：始域・終域は任意の単体集合。
使われ方：Kerodon Proposition 7.2.1.5(1)、Quillen A の必要性。 -/
lemma IsRightCofinal.isWeakHomotopyEquivalence {A B : SSet.{u}} {i : A ⟶ B}
    (hi : IsRightCofinal i) : IsWeakHomotopyEquivalence i := by
  intro Z hZ
  exact (cofinalProductTest_pre_isSimplicialHomotopyEquivalence (𝟙 B) i Z
    (hi (Z ⊗ B) (snd Z B))).mapPiZero_bijective

end SerrePositivity.InfinityCategories
