module

public import SerrePositivity.EInfinity.PowerOperation.MayCyclicGroup
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ArityProjectiveResolution
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ResolutionAugmentationComparison
public import Mathlib.RepresentationTheory.Coinduced

/-!
# May の巡回解像度から BE の実 arity への同変比較

May, Definitions 1.2・2.1 の W と、BE の E(p) を同じ実置換部分群の表現として比べる。
係数環は任意の可換環とし、群位数の可逆性は要求しない。
増大と比較射を指定し、射影解像度の比較による同変鎖ホモトピーを保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.EInfinity.BarrattEccles
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- May の右回転を用いた、指定増大を持つ周期射影解像度。 -/
def mayResolution : ProjectiveResolution (Rep.trivial k (MayCyclicGroup.{u} p) k) :=
  Rep.FiniteCyclicGroup.resolution k (mayCyclicGenerator p) (mayCyclicGenerator_generates p)

/-- 元の BE の arity の解像度を、同じ実巡回部分群へ制限する。 -/
def mayArityResolution : ProjectiveResolution (Rep.trivial k (MayCyclicGroup.{u} p) k) :=
  (Rep.resFunctor.{u} (k := k) (mayCyclicPermutation.{u} p).range.subtype).mapProjectiveResolution
    (arityProjectiveResolution k p)

/-- 単位の指定増大を保つ、W→E(p) の実同変鎖写像。 -/
def mayResolutionComparison : (mayResolution p k).complex ⟶ (mayArityResolution p k).complex :=
  ProjectiveResolution.lift (𝟙 _) (mayResolution p k) (mayArityResolution p k)

@[reassoc]
lemma mayResolutionComparison_augmentation :
    mayResolutionComparison p k ≫ (mayArityResolution p k).π = (mayResolution p k).π := by
  have h := ProjectiveResolution.lift_commutes (𝟙 _) (mayResolution p k) (mayArityResolution p k)
  rw [(ChainComplex.single₀ (Rep.{u} k (MayCyclicGroup.{u} p))).map_id, Category.comp_id] at h
  exact h

/-- 同じ指定順射を持つ、実巡回表現の圏での鎖ホモトピー同値。 -/
def mayResolutionComparisonEquiv :
    HomotopyEquiv (mayResolution p k).complex (mayArityResolution p k).complex :=
  resolutionHomotopyEquivOfAugmentation (mayResolution p k) (mayArityResolution p k)
    (mayResolutionComparison p k) (mayResolutionComparison_augmentation p k)

lemma mayResolutionComparisonEquiv_hom :
    (mayResolutionComparisonEquiv p k).hom = mayResolutionComparison p k := rfl

/-- 増大を保つ別の同変比較射は、同じ指定比較射と鎖ホモトピック。 -/
def mayResolutionComparisonHomotopy
    (f : (mayResolution p k).complex ⟶ (mayArityResolution p k).complex)
    (hf : f ≫ (mayArityResolution p k).π = (mayResolution p k).π) :
    Homotopy f (mayResolutionComparison p k) := by
  apply ProjectiveResolution.liftHomotopy (P := mayResolution p k)
    (Q := mayArityResolution p k) (𝟙 _) f (mayResolutionComparison p k)
  · rw [(ChainComplex.single₀ (Rep.{u} k (MayCyclicGroup.{u} p))).map_id, Category.comp_id]
    exact hf
  · rw [(ChainComplex.single₀ (Rep.{u} k (MayCyclicGroup.{u} p))).map_id, Category.comp_id]
    exact mayResolutionComparison_augmentation p k

end SerrePositivity.EInfinity.PowerOperation
