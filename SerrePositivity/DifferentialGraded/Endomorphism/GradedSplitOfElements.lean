module
public import SerrePositivity.DifferentialGraded.Endomorphism.ZeroHomComponents

/-! # 零次数Hom要素の行列恒等式から全次数分裂を復元する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 分裂の証拠となる零次数要素にchain map条件を課さない構成子。 -/
def moduleGradedSplitOfHomElements {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (a : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) M)).X 0)
    (b : (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N)).X 0)
    (hfa : forward A (D := RightModule A D)
      (x := ForgetEnrichment.to (Complex A) M) (y := ForgetEnrichment.to (Complex A) N)
      (z := ForgetEnrichment.to (Complex A) M) (endomorphismClosedElement A D f) a (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val)
    (hbg : forward A (D := RightModule A D)
      (x := ForgetEnrichment.to (Complex A) P) (y := ForgetEnrichment.to (Complex A) N)
      (z := ForgetEnrichment.to (Complex A) P) b (endomorphismClosedElement A D g) (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) P)).val)
    (hba : forward A (D := RightModule A D)
      (x := ForgetEnrichment.to (Complex A) P) (y := ForgetEnrichment.to (Complex A) N)
      (z := ForgetEnrichment.to (Complex A) M) b a (zero_add 0) = 0)
    (hdec : (forward A (D := RightModule A D)
      (x := ForgetEnrichment.to (Complex A) N) (y := ForgetEnrichment.to (Complex A) M)
      (z := ForgetEnrichment.to (Complex A) N) a (endomorphismClosedElement A D f) (zero_add 0) +
      forward A (D := RightModule A D)
        (x := ForgetEnrichment.to (Complex A) N) (y := ForgetEnrichment.to (Complex A) P)
        (z := ForgetEnrichment.to (Complex A) N) (endomorphismClosedElement A D g) b (zero_add 0) :
        (moduleHom A D (ForgetEnrichment.to (Complex A) N)
          (ForgetEnrichment.to (Complex A) N)).X 0) =
        (unitElement A (ForgetEnrichment.to (Complex A) N)).val)
    (hfg : f ≫ g = 0) : ModuleGradedSplit A D f g where
  retraction x n := zeroHomComponent A D a x n
  section_ x n := zeroHomComponent A D b x n
  inclusion_retraction x n := by
    have h := congrArg (fun z => zeroHomComponent A D
      (M := ForgetEnrichment.to (Complex A) M)
      (N := ForgetEnrichment.to (Complex A) M) z x n) hfa
    simp only [zeroHomComponent_forward, zeroHomComponent_closed, zeroHomComponent_unit] at h
    exact h
  section_projection x n := by
    have h := congrArg (fun z => zeroHomComponent A D
      (M := ForgetEnrichment.to (Complex A) P)
      (N := ForgetEnrichment.to (Complex A) P) z x n) hbg
    simp only [zeroHomComponent_forward, zeroHomComponent_closed, zeroHomComponent_unit] at h
    exact h
  section_retraction x n := by
    have h := congrArg (fun z => zeroHomComponent A D
      (M := ForgetEnrichment.to (Complex A) P)
      (N := ForgetEnrichment.to (Complex A) M) z x n) hba
    simp only [zeroHomComponent_forward, zeroHomComponent_zero] at h
    exact h
  inclusion_projection := hfg
  decomposition x n := by
    have h := congrArg (fun z => zeroHomComponent A D
      (M := ForgetEnrichment.to (Complex A) N)
      (N := ForgetEnrichment.to (Complex A) N) z x n) hdec
    have hadd := zeroHomComponent_add A D
      (M := ForgetEnrichment.to (Complex A) N) (N := ForgetEnrichment.to (Complex A) N)
      (forward A (D := RightModule A D) a (endomorphismClosedElement A D f) (zero_add 0))
      (forward A (D := RightModule A D) (endomorphismClosedElement A D g) b (zero_add 0)) x n
    have h' := hadd.symm.trans h
    simp only [zeroHomComponent_forward, zeroHomComponent_closed, zeroHomComponent_unit] at h'
    exact h'
  retraction_naturality x y p i j hij f := zeroHomComponent_naturality A D a x y p i j hij f
  section_naturality x y p i j hij f := (zeroHomComponent_naturality A D b x y p i j hij f).symm

end SerrePositivity.DifferentialGraded
