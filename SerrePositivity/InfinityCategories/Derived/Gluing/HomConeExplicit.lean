module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeHomotopyAction

/-! 元の双加群作用と閉射の第三成分を使う、Hom の標準 cone の明示的な比較。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories

lemma dgGluingConeSquareMap_transport {R : Type u} [CommRing R] {P Q S T : Complex R}
    (f : P ⟶ Q) (g g' : S ⟶ T) (μ : P ⟶ S) (ν : Q ⟶ T)
    (h h' : Cochain P T (-1))
    (hh : δ (-1) 0 h + Cochain.ofHom (μ ≫ g - f ≫ ν) = 0)
    (hh' : δ (-1) 0 h' + Cochain.ofHom (μ ≫ g' - f ≫ ν) = 0)
    (hg : g = g') (he : h = h') :
    dgGluingConeSquareMap f g μ ν h hh ≫
      (eqToIso (congrArg (fun a : S ⟶ T => mappingCone a) hg)).hom =
    dgGluingConeSquareMap f g' μ ν h' hh' := by
  subst g'
  subst h'
  simp

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "μ" => dgGluingDifference R C D M X Y
local notation "ν" => dgGluingDifference R C D M X Z
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "k" => dgGluingPostcomposition R C D M X Y Z f
local notation "B" => dgGluingCommaObject R C D M Y
local notation "C'" => dgGluingCommaObject R C D M Z

/-- Hom cone の下辺を、同じ閉右成分による双加群作用として固定する。 -/
def dgGluingHomConeAction : M.value X.left Y.right ⟶ M.value X.left Z.right :=
  (moduleEvaluation R C X.left).map
    (M.toFunctor.onClosed.map ((dgGluingRight R C D M).onClosed.map f))

/-- Hom cone の比較 cochain を、閉射の同じ第三成分の評価で固定する。 -/
def dgGluingHomConeThird :
    Cochain (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right)
      (M.value X.left Z.right) (-1) :=
  -(Cochain.ofHom biprod.fst).comp
    (dgGluingCommaClosedSquareHomotopy R C D M B C'
      ((dgGluingToComma R C D M).onClosed.map f) X.left) (zero_add (-1))

lemma dgGluingHomConeRecovered_boundary :
    δ (-1) 0 (dgGluingHomConeHomotopy R C D M X Y Z f) +
      Cochain.ofHom (μ ≫ dgGluingHomConeBottom R C D M X Y Z f - p ≫ ν) = 0 := by
  have he := dgGluingCoconeExtractHomotopy_boundary μ ν p k
    (dgGluingPostcomposition_fst R C D M X Y Z f)
  have hn : dgGluingCoconeExtractHomotopy μ ν k =
      dgGluingHomConeHomotopy R C D M X Y Z f := rfl
  have hg : dgGluingCoconeExtractBottom μ ν p k
      (dgGluingPostcomposition_fst R C D M X Y Z f) =
      dgGluingHomConeBottom R C D M X Y Z f := rfl
  rw [hn, hg] at he
  exact he

lemma dgGluingHomConeThird_boundary :
    δ (-1) 0 (dgGluingHomConeThird R C D M X Y Z f) +
      Cochain.ofHom (μ ≫ dgGluingHomConeAction R C D M X Y Z f - p ≫ ν) = 0 := by
  have he := dgGluingHomConeRecovered_boundary R C D M X Y Z f
  rw [dgGluingHomConeHomotopy_action, dgGluingHomConeBottom_action] at he
  exact he

/-- 元の作用と第三成分による、同じ Hom cone の明示的な係数鎖写像。 -/
def dgGluingHomConeExplicitCoefficient : mappingCone p ⟶
    mappingCone (dgGluingHomConeAction R C D M X Y Z f) :=
  dgGluingConeSquareMap p (dgGluingHomConeAction R C D M X Y Z f) μ ν
    (dgGluingHomConeThird R C D M X Y Z f) (dgGluingHomConeThird_boundary R C D M X Y Z f)

def dgGluingHomConeActionIso : mappingCone (dgGluingHomConeBottom R C D M X Y Z f) ≅
    mappingCone (dgGluingHomConeAction R C D M X Y Z f) :=
  eqToIso (congrArg (fun a : M.value X.left Y.right ⟶ M.value X.left Z.right => mappingCone a)
    (dgGluingHomConeBottom_action R C D M X Y Z f))

lemma dgGluingHomConeCoefficient_transport :
    dgGluingHomConeCoefficient R C D M X Y Z f ≫
      (dgGluingHomConeActionIso R C D M X Y Z f).hom =
    dgGluingHomConeExplicitCoefficient R C D M X Y Z f := by
  exact dgGluingConeSquareMap_transport p (dgGluingHomConeBottom R C D M X Y Z f)
    (dgGluingHomConeAction R C D M X Y Z f) μ ν
    (dgGluingHomConeHomotopy R C D M X Y Z f) (dgGluingHomConeThird R C D M X Y Z f)
    (dgGluingHomConeRecovered_boundary R C D M X Y Z f)
    (dgGluingHomConeThird_boundary R C D M X Y Z f)
    (dgGluingHomConeBottom_action R C D M X Y Z f)
    (dgGluingHomConeHomotopy_action R C D M X Y Z f)

/-- 元の Hom 後合成の標準 cone と、明示した係数の mapping cocone の鎖同型。 -/
def dgGluingHomConeExplicitIso : mappingCone k ≅
    mappingCocone (dgGluingHomConeExplicitCoefficient R C D M X Y Z f) :=
  dgGluingHomConeIso R C D M X Y Z f ≪≫
    complexMappingCoconeMapIso (dgGluingHomConeCoefficient R C D M X Y Z f)
      (dgGluingHomConeExplicitCoefficient R C D M X Y Z f) (Iso.refl _)
      (dgGluingHomConeActionIso R C D M X Y Z f) (by
        simpa only [Iso.refl_hom, Category.id_comp] using
          dgGluingHomConeCoefficient_transport R C D M X Y Z f)

end SerrePositivity.InfinityCategories
