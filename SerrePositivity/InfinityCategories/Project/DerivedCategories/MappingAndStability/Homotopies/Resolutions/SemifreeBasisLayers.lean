module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeBasisColimit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ZeroBasisSpheres
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.BasisCut
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.RingGradedSplit

/-! # Semibasis の各高さの自由商

概要：高さで切った段の次の商を、ちょうど一つの高さの基底元から作る。
方針：低い高さと一つ上の高さへの座標射影で次数付き分裂を構成する。
規約：商は微分零の自由複体として具体化する。使われ方：既存 semifree filtration。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {S : Type u} [CommRing S] {P : Complex S} (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P)

/-- 概要：高さがちょうど n の基底元の線形包。
方針：高さの等号で基底を選ぶ。規約：各次数で定義する。
使われ方：段の商の underlying 加群。 -/
def layerSubmodule (n : ℕ) (k : ℤ) : Submodule S (P.X k) :=
  Submodule.span S ((B.basis k) '' {i | B.height k i = n})

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (layerSubmodule)


/-- 概要：一つの高さの部分加群には、その高さの基底元による基底がある。
方針：一次独立な部分族の線形包の基底。規約：添字に有限性は不要。
使われ方：商の自由 sphere 表示。 -/
def layerBasis (n : ℕ) (k : ℤ) :
    Module.Basis {i : B.Index k // B.height k i = n} S (B.layerSubmodule n k) := by
  unfold layerSubmodule
  rw [Set.image_eq_range]
  exact Module.Basis.span ((B.basis k).linearIndependent.comp
    (fun i : {i : B.Index k // B.height k i = n} => i.val) Subtype.val_injective)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (layerBasis)


/-- 概要：一つの高さの部分加群を微分零の複体にする。
方針：全ての微分を零に置く。規約：元の微分を制限する構成ではない。
使われ方：高さ filtration の自由商。 -/
def layerComplex (n : ℕ) : Complex S :=
  CochainComplex.of (fun k => ModuleCat.of S (B.layerSubmodule n k))
    (fun _ => 0) (fun _ => by simp only [zero_comp])

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (layerComplex)


/-- 概要：同じ高さの線形包は、その高さ以下の段に含まれる。
方針：生成元の高さの等号から不等号を得る。
規約：微分を忘れた部分加群の包含。使われ方：商からの次数付き section。 -/
theorem layerSubmodule_le_stage (n : ℕ) (k : ℤ) :
    B.layerSubmodule n k ≤ B.stageSubmodule n k := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  exact hi.le

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (layerSubmodule_le_stage)


/-- 概要：低い高さへの座標射影による次数付き retraction。
方針：高さ ≤ n の座標だけを残す。
規約：始域は第 n+1 段。使われ方：分裂の retraction。 -/
def lowRetraction (n : ℕ) (k : ℤ) :
    (B.stageComplex (n + 1)).X k ⟶ (B.stageComplex n).X k :=
  ModuleCat.ofHom (LinearMap.codRestrict _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut (B.basis k) {i | B.height k i ≤ n}).comp
      (B.stageSubmodule (n + 1) k).subtype)
    (fun x => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_mem (B.basis k) _ x.val))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (lowRetraction)


/-- 概要：第 n+1 段からちょうど高さ n+1 の座標を取り出す。
方針：高さの等号による射影の値域を制限する。
規約：次数付きの射として定義する。使われ方：自由商への chain map の成分。 -/
def highProjection (n : ℕ) (k : ℤ) :
    (B.stageComplex (n + 1)).X k ⟶ (B.layerComplex (n + 1)).X k :=
  ModuleCat.ofHom (LinearMap.codRestrict _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut (B.basis k) {i | B.height k i = n + 1}).comp
      (B.stageSubmodule (n + 1) k).subtype)
    (fun x => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_mem (B.basis k) _ x.val))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (highProjection)


/-- 概要：高さ n+1 の線形包の第 n+1 段への次数付き包含。
方針：部分加群の包含を使う。規約：chain map 条件は課さない。
使われ方：自由商からの section。 -/
def highSection (n : ℕ) (k : ℤ) :
    (B.layerComplex (n + 1)).X k ⟶ (B.stageComplex (n + 1)).X k :=
  ModuleCat.ofHom (Submodule.inclusion (B.layerSubmodule_le_stage (n + 1) k))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (highSection)


private theorem ComplexSemifreeBasis.low_high_disjoint (n : ℕ) (k : ℤ) :
    Disjoint {i : B.Index k | B.height k i ≤ n} {i | B.height k i = n + 1} := by
  apply Set.disjoint_left.mpr
  intro i hi hj
  change B.height k i ≤ n at hi
  change B.height k i = n + 1 at hj
  omega

/-- 概要：低い段の包含と retraction の合成は恒等。
方針：低い段の要素に対する座標射影は恒等である。
規約：各次数での線形等式。使われ方：次数付き分裂の単位則。 -/
theorem inclusion_lowRetraction (n : ℕ) (k : ℤ) :
    (B.stageMap (Nat.le_succ n)).f k ≫ B.lowRetraction n k = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_eq_self (B.basis k) _ x.property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (inclusion_lowRetraction)


/-- 概要：高い section と射影の合成は恒等。
方針：高さ n+1 の線形包上で同じ高さへの座標射影は恒等。
規約：各次数での線形等式。使われ方：次数付き分裂の単位則。 -/
theorem highSection_projection (n : ℕ) (k : ℤ) :
    B.highSection n k ≫ B.highProjection n k = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_eq_self (B.basis k) _ x.property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (highSection_projection)


/-- 概要：高い section の像の低い retraction は零。
方針：高い座標と低い座標は互いに素である。
規約：微分との可換性を使わない。使われ方：次数付き分裂の直交性。 -/
theorem highSection_lowRetraction (n : ℕ) (k : ℤ) :
    B.highSection n k ≫ B.lowRetraction n k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut (B.basis k) {i | B.height k i ≤ n} x.val = 0
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_eq_self (B.basis k) {i | B.height k i = n + 1} x.property]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_disjoint (B.basis k) _ _ (B.low_high_disjoint n k) x.val

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (highSection_lowRetraction)


/-- 概要：低い段の包含と高い射影の合成は零。
方針：低い座標の線形包から高い座標へ射影すると零。
規約：各次数の等式。使われ方：段の商の複体の射の定義。 -/
theorem inclusion_highProjection (n : ℕ) (k : ℤ) :
    (B.stageMap (Nat.le_succ n)).f k ≫ B.highProjection n k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut (B.basis k) {i | B.height k i = n + 1} x.val = 0
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_eq_self (B.basis k) {i | B.height k i ≤ n} x.property]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_disjoint (B.basis k) _ _ (B.low_high_disjoint n k).symm x.val

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (inclusion_highProjection)


/-- 概要：次の段の微分に高い射影を施すと零である。
方針：微分の像が一つ低い段に入ることを使う。
規約：商の高さは n+1。使われ方：高い射影の chain map 条件。 -/
theorem highProjection_differential (n : ℕ) (k : ℤ)
    (x : B.stageSubmodule (n + 1) k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut (B.basis (k + 1)) {i | B.height (k + 1) i = n + 1}
      ((P.d k (k + 1)) x.val) = 0 := by
  have hx := B.differential_mem_previous n k x.property
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_eq_self (B.basis (k + 1)) {i | B.height (k + 1) i ≤ n} hx]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_disjoint (B.basis (k + 1)) _ _
    (B.low_high_disjoint n (k + 1)).symm _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (highProjection_differential)


/-- 概要：高い射影は自由商への複体の射を与える。
方針：商の微分零と、微分の像の高い射影の零性を照合する。
規約：元の複体の微分は任意。使われ方：semifree filtration の商射。 -/
def layerQuotientMap (n : ℕ) : B.stageComplex (n + 1) ⟶ B.layerComplex (n + 1) :=
  CochainComplex.ofHom (B.highProjection n) (by
    intro k
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis.stageComplex, layerComplex]
    rw [CochainComplex.of_d, CochainComplex.of_d, comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (B.highProjection_differential n k x).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (layerQuotientMap)


/-- 概要：第 n+1 段の要素は低い段と一つ上の高さの和に分解する。
方針：高さ ≤ n+1 の基底元を高さ ≤ n と高さ = n+1 に分ける。
規約：両集合は互いに素。使われ方：次数付き分裂の分解則。 -/
theorem low_high_decomposition (n : ℕ) (k : ℤ) :
    B.lowRetraction n k ≫ (B.stageMap (Nat.le_succ n)).f k +
      B.highProjection n k ≫ B.highSection n k = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut (B.basis k) {i | B.height k i ≤ n} x.val +
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut (B.basis k) {i | B.height k i = n + 1} x.val = x.val
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.basisCoordinateCut_add (B.basis k) _ _ (B.low_high_disjoint n k)
  apply Submodule.span_mono (Set.image_mono ?_) x.property
  intro i hi
  change B.height k i ≤ n + 1 at hi
  change B.height k i ≤ n ∨ B.height k i = n + 1
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (low_high_decomposition)


/-- 概要：各高さの微分零複体の一点加群は自由 sphere 表示を持つ。
方針：各次数の部分基底と微分零を既存の表示補題に適用する。
規約：高さは任意の自然数。使われ方：filtration の商の自由表示。 -/
def layerSpherePresentation (n : ℕ) : ModuleSphereFreePresentation S PUnit.{1}
    (ForgetEnrichment.of (Complex S) (ringModule S (B.layerComplex n))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.zeroBasisModuleSpherePresentation S (B.layerBasis n)
    (fun k => by dsimp only [layerComplex]; rw [CochainComplex.of_d])

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (layerSpherePresentation)


/-- 概要：高さ零の初期段の一点加群は自由 sphere 表示を持つ。
方針：初期段の微分零と、部分基底を使う。
規約：高さ零を初期段にする。使われ方：semifree filtration の初期データ。 -/
def initialSpherePresentation : ModuleSphereFreePresentation S PUnit.{1}
    (ForgetEnrichment.of (Complex S) (ringModule S (B.stageComplex 0))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.zeroBasisModuleSpherePresentation S (B.stageBasis 0) (fun k => by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis.stageComplex]
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact B.differential_eq_zero_on_stageZero k x.property)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (initialSpherePresentation)


/-- 概要：段の包含と自由商への射は一点 dg 加群で次数付きに分裂する。
方針：座標射影の分解則を既存 `ModuleGradedSplit` へ転送する。
規約：section と retraction は次数付き写像。使われ方：既存 filtration の構成。 -/
def layerModuleGradedSplit (n : ℕ) : ModuleGradedSplit S PUnit.{1}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap S (B.stageMap (Nat.le_succ n)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap S (B.layerQuotientMap n)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexGradedSplit S _ _ (B.lowRetraction n) (B.highSection n)
    (B.inclusion_lowRetraction n) (B.highSection_projection n)
    (B.highSection_lowRetraction n)
    (by
      apply HomologicalComplex.Hom.ext
      funext k
      exact B.inclusion_highProjection n k)
    (B.low_high_decomposition n)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (layerModuleGradedSplit)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
