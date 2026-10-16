module
public import SerrePositivity.DifferentialGraded.Tensor.HomElements
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunction
public import SerrePositivity.DifferentialGraded.Module.GradedSplitElements

/-! # 全作用と可換するgraded splittingのbalanced tensorへの像 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 固定左加群とのtensor写像を、元のbalanced tensor対象間の射として読む。 -/
def rightTensorMap {M N : ModuleCategory A D} (L : LeftModule A D) (f : M ⟶ N) :
    obj A D (ForgetEnrichment.to (Complex A) M) L ⟶
      obj A D (ForgetEnrichment.to (Complex A) N) L :=
  (rightTensorFunctor A D L).map f

lemma rightTensorMap_element {M N : ModuleCategory A D} (L : LeftModule A D)
    (f : M ⟶ N) (x : D) {r s n : ℤ}
    (m : ((ForgetEnrichment.to (Complex A) M).obj (op x)).X r)
    (v : (L.obj x).X s) (hn : r + s = n) :
    (rightTensorMap A D L f).f n
      (element A D (ForgetEnrichment.to (Complex A) M) L x m v hn) =
    element A D (ForgetEnrichment.to (Complex A) N) L x
      (((moduleEvaluation A D x).map f).f r m) v hn := by
  have h := map_element A D f (𝟙 (ForgetEnrichment.of (Complex A) L)) x m v hn
  simpa only [rightTensorMap, rightTensorFunctor, ForgetEnrichment.to_of,
    CategoryTheory.Functor.map_id,
    HomologicalComplex.id_f, ModuleCat.id_apply] using h

variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- tensor後のretractionは閉じているとは限らない次数零cochain。 -/
def tensorRetractionCochain (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    Cochain (obj A D (ForgetEnrichment.to (Complex A) N) L)
      (obj A D (ForgetEnrichment.to (Complex A) M) L) 0 :=
  (rightHomMap A D (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) M) L).f 0 s.retractionElement

/-- tensor後のsectionも主Homから得た次数零cochain。 -/
def tensorSectionCochain (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    Cochain (obj A D (ForgetEnrichment.to (Complex A) P) L)
      (obj A D (ForgetEnrichment.to (Complex A) N) L) 0 :=
  (rightHomMap A D (ForgetEnrichment.to (Complex A) P)
    (ForgetEnrichment.to (Complex A) N) L).f 0 s.sectionElement

lemma tensorRetractionCochain_element (s : ModuleGradedSplit A D f g) (L : LeftModule A D)
    (x : D) {r t a : ℤ} (ha : r + t = a)
    (m : ((ForgetEnrichment.to (Complex A) N).obj (op x)).X r) (v : (L.obj x).X t) :
    (tensorRetractionCochain A D s L).v a a (add_zero a)
      (element A D (ForgetEnrichment.to (Complex A) N) L x m v ha) =
    element A D (ForgetEnrichment.to (Complex A) M) L x (s.retraction x r m) v ha := by
  change (((rightHomMap A D (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) M) L).f 0 s.retractionElement).v a a (add_zero a))
    (element A D (ForgetEnrichment.to (Complex A) N) L x m v ha) = _
  rw [rightHomMap_element_of_sum A D L _ x m v ha (zero_add r) (add_zero a),
    s.retractionElement_π]
  rfl

lemma tensorSectionCochain_element (s : ModuleGradedSplit A D f g) (L : LeftModule A D)
    (x : D) {r t a : ℤ} (ha : r + t = a)
    (m : ((ForgetEnrichment.to (Complex A) P).obj (op x)).X r) (v : (L.obj x).X t) :
    (tensorSectionCochain A D s L).v a a (add_zero a)
      (element A D (ForgetEnrichment.to (Complex A) P) L x m v ha) =
    element A D (ForgetEnrichment.to (Complex A) N) L x (s.section_ x r m) v ha := by
  change (((rightHomMap A D (ForgetEnrichment.to (Complex A) P)
    (ForgetEnrichment.to (Complex A) N) L).f 0 s.sectionElement).v a a (add_zero a))
    (element A D (ForgetEnrichment.to (Complex A) P) L x m v ha) = _
  rw [rightHomMap_element_of_sum A D L _ x m v ha (zero_add r) (add_zero a),
    s.sectionElement_π]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
