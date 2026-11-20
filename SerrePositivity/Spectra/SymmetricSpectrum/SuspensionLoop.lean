module

public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorLevelEvaluation

/-! # 円によるスペクトルの懸垂・ループの随伴 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet

/-- 円の各段のsmashによる懸垂関手。 -/
def suspensionFunctor : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  pointwiseTensorFunctor (circle : PointedSimplicialSet.{u})

/-- 円からの各段の内部Homによるループ関手。 -/
def loopFunctor : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  cotensorFunctor (circle : PointedSimplicialSet.{u})

/-- 対称スペクトルの懸垂。 -/
def suspension (E : SymmetricSpectrum.{u}) : SymmetricSpectrum.{u} := suspensionFunctor.obj E

/-- 対称スペクトルのループ。 -/
def loops (E : SymmetricSpectrum.{u}) : SymmetricSpectrum.{u} := loopFunctor.obj E

/-- 懸垂とループの随伴。 -/
def suspensionLoopAdjunction : suspensionFunctor.{u} ⊣ loopFunctor.{u} :=
  pointwiseTensorCotensorAdjunction (circle : PointedSimplicialSet.{u})

/-- 懸垂からの射とループへの射の自然なHom同値。 -/
def suspensionLoopHomEquiv (E F : SymmetricSpectrum.{u}) :
    (suspension E ⟶ F) ≃ (E ⟶ loops F) := suspensionLoopAdjunction.homEquiv E F

/-- 懸垂の各段は円との通常のsmash。 -/
lemma suspension_level (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (suspension E) q = (circle : PointedSimplicialSet.{u}) ⊗ level E q := rfl

/-- ループの各段は円からの通常の内部Hom。 -/
lemma loops_level (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (loops E) q = (ihom (circle : PointedSimplicialSet.{u})).obj (level E q) := rfl

/-- 懸垂・ループの随伴の単位。 -/
def suspensionLoopUnit (E : SymmetricSpectrum.{u}) : E ⟶ loops (suspension E) :=
  suspensionLoopAdjunction.unit.app E

/-- 懸垂・ループの随伴の余単位。 -/
def suspensionLoopCounit (E : SymmetricSpectrum.{u}) : suspension (loops E) ⟶ E :=
  suspensionLoopAdjunction.counit.app E

/-- 懸垂とループのHom同値は原変数スペクトルの射に関して自然。 -/
lemma suspensionLoopHomEquiv_naturality_left {E E' F : SymmetricSpectrum.{u}}
    (f : E ⟶ E') (g : suspension E' ⟶ F) :
    suspensionLoopHomEquiv E F (suspensionFunctor.map f ≫ g) =
      f ≫ suspensionLoopHomEquiv E' F g :=
  suspensionLoopAdjunction.homEquiv_naturality_left f g

/-- 懸垂とループのHom同値は値域スペクトルの射に関して自然。 -/
lemma suspensionLoopHomEquiv_naturality_right {E F F' : SymmetricSpectrum.{u}}
    (f : suspension E ⟶ F) (g : F ⟶ F') :
    suspensionLoopHomEquiv E F' (f ≫ g) =
      suspensionLoopHomEquiv E F f ≫ loopFunctor.map g :=
  suspensionLoopAdjunction.homEquiv_naturality_right f g

/-- 単位と余単位は懸垂側のtriangle則を満たす。 -/
lemma suspensionLoop_left_triangle (E : SymmetricSpectrum.{u}) :
    suspensionFunctor.map (suspensionLoopUnit E) ≫ suspensionLoopCounit (suspension E) =
      𝟙 (suspension E) := suspensionLoopAdjunction.left_triangle_components E

/-- 単位と余単位はループ側のtriangle則を満たす。 -/
lemma suspensionLoop_right_triangle (E : SymmetricSpectrum.{u}) :
    suspensionLoopUnit (loops E) ≫ loopFunctor.map (suspensionLoopCounit E) = 𝟙 (loops E) :=
  suspensionLoopAdjunction.right_triangle_components E

end SerrePositivity.SymmetricSpectrum
