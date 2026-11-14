module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneConePullback
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLoopProperties
public import SerrePositivity.KST.Spectra.LoopFiber
public import SerrePositivity.KST.Spectra.PointedFiberComparison

/-!
# 有限極限を保つ点付き関手の cone fiber 比較

DAG XIII §2.2 の Ω 比較への前段。実際の cone の二射と点付き fiber の包含を保持する。
ここでは Γ と loop Γ の両方に同じ極限の普遍性を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.KST.Spectra
variable (A : Type u) [CommRing A]
variable (F : Complex A ⥤ PointedSimplicialSet.{u})
  [PreservesFiniteLimits F] [F.PreservesZeroMorphisms]

/-- 同じ回転 cone の kernel を関手で移して得る、指定 fiber との厳密な同型。 -/
def pointedConeFiberIso {M N : Complex A} (f : M ⟶ N) :
    F.obj N ≅ pointedFiber (F.map (mappingCone.triangle f).mor₃) :=
  ((KernelFork.ofι (mappingCone.inr f)
      (mappingCone.triangleRotateShortComplex f).zero).mapIsLimit
    (coneRotateShortComplex_shortExact A f).fIsKernel F).conePointUniqueUpToIso
      (pointedFiberKernelIsLimit (F.map (mappingCone.triangle f).mor₃))

/-- 同型は元の cone の指定包含を変えない。 -/
@[reassoc (attr := simp)]
lemma pointedConeFiberIso_hom_ι {M N : Complex A} (f : M ⟶ N) :
    (pointedConeFiberIso A F f).hom ≫
      pointedFiberι (F.map (mappingCone.triangle f).mor₃) = F.map (mappingCone.inr f) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- 比較は関手間の自然変換にも厳密に自然である。 -/
lemma pointedConeFiberIso_naturality
    (G : Complex A ⥤ PointedSimplicialSet.{u})
    [PreservesFiniteLimits G] [G.PreservesZeroMorphisms]
    (η : F ⟶ G) {M N : Complex A} (f : M ⟶ N) :
    (pointedConeFiberIso A F f).hom ≫
      PointedFiberComparison.map (F.map (mappingCone.triangle f).mor₃)
        (G.map (mappingCone.triangle f).mor₃)
        (η.app (mappingCone f)) (η.app (M⟦(1 : ℤ)⟧))
        (η.naturality (mappingCone.triangle f).mor₃) =
      η.app N ≫ (pointedConeFiberIso A G f).hom := by
  apply pointedFiber_hom_ext
  rw [Category.assoc, PointedFiberComparison.map_ι, ← Category.assoc,
    pointedConeFiberIso_hom_ι, Category.assoc, pointedConeFiberIso_hom_ι]
  exact η.naturality (mappingCone.inr f)

end SerrePositivity.EInfinity.PowerOperation
