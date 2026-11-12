module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSuspensionNaturality
public import SerrePositivity.KST.Spectra.KanSequenceCategory

/-!
# 指定された Γ の Kan スペクトル列

DAG XIII §2.2 のスペクトル忘却への前段。各段と指定 suspension 射を束ねる。
ここではまだ Ω 条件・構造射の単射性を主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma levelSigma_naturality {M N : Complex A} (f : M ⟶ N) (r : ℕ) :
    PointedObject.smashMap (𝟙 PointedSimplicialSet.circle.{u})
      ((levelPointedFunctor A r).map f) ≫ levelSigma A N r =
    levelSigma A M r ≫ (levelPointedFunctor A (r + 1)).map f := by
  dsimp only [levelSigma]
  change PointedObject.smashMap (𝟙 PointedSimplicialSet.circle.{u})
    ((gammaPointedFunctor A).map (f⟦(r : ℤ)⟧')) ≫
      gammaSuspension A (N⟦(r : ℤ)⟧) ≫ _ = _
  rw [← Category.assoc, gammaSuspension_naturality, Category.assoc,
    ← Functor.map_comp]
  change gammaSuspension A (M⟦(r : ℤ)⟧) ≫ _ =
    gammaSuspension A (M⟦(r : ℤ)⟧) ≫
      (gammaPointedFunctor A).map
        ((shiftFunctorAdd' (Complex A) (r : ℤ) 1 ((r + 1 : ℕ) : ℤ)
          (by omega)).inv.app M) ≫
      (gammaPointedFunctor A).map (f⟦((r + 1 : ℕ) : ℤ)⟧')
  rw [← Functor.map_comp]
  congr 1
  apply congrArg ((gammaPointedFunctor A).map)
  exact (shiftFunctorAdd' (Complex A) (r : ℤ) 1 ((r + 1 : ℕ) : ℤ)
    (by omega)).inv.naturality f

/-- Ω 条件を入れる前の、実際の Γ の Kan 列。 -/
def eilenbergMacLaneSequence (M : Complex A) : KST.Spectra.KanSequence.{u} where
  level r := ⟨(levelPointedFunctor A r).obj M, inferInstance⟩
  sigma r := levelSigma A M r

/-- 複体の射は、指定構造射と厳密に可換な列の射を与える。 -/
def eilenbergMacLaneSequenceFunctor : Complex A ⥤ KST.Spectra.KanSequence.{u} where
  obj M := eilenbergMacLaneSequence A M
  map f := {
    app r := (levelPointedFunctor A r).map f
    comm r := levelSigma_naturality A f r }
  map_id M := by
    apply KST.Spectra.KanSequence.Hom.ext_app
    intro r
    exact (levelPointedFunctor A r).map_id M
  map_comp f g := by
    apply KST.Spectra.KanSequence.Hom.ext_app
    intro r
    exact (levelPointedFunctor A r).map_comp f g

end SerrePositivity.EInfinity.PowerOperation
