module

public import SerrePositivity.KST.Spectra.PointedFiber
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：点つき fiber の kernel としての普遍性と loop による保存。
方針：点つき fiber の既存の持ち上げから kernel fork の極限性を証明し、右随伴で移す。
規約：通常の点つき圏の厳密な同型であり、∞ 極限の主張ではない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。fiber 列の Ω 条件。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき fiber の包含による kernel fork。
方針：包含と元の射の合成が零射である証明を使う。
規約：Kan 性を要求しない。
使われ方：Goerss–Jardine I §7、HA §1.4.2。右随伴による fiber の保存。 -/
def pointedFiberKernelFork {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) : KernelFork p :=
  KernelFork.ofι (pointedFiberι p) (pointedFiberι_comp p)

/-- 概要：点つき fiber の kernel fork は極限。
方針：零合成からの既存の持ち上げと包含後の一意性を使う。
規約：通常の点つき圏の kernel の普遍性。
使われ方：Goerss–Jardine I §7、HA §1.4.2。loop が保存する fiber の円錐。 -/
def pointedFiberKernelIsLimit {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    IsLimit (pointedFiberKernelFork p) :=
  KernelFork.IsLimit.ofι (pointedFiberι p) (pointedFiberι_comp p)
    (fun f hf ↦ pointedFiberLiftOfZero p f hf)
    (fun f hf ↦ pointedFiberLiftOfZero_ι p f hf)
    (fun f hf _m hm ↦ pointedFiber_hom_ext p (hm.trans (pointedFiberLiftOfZero_ι p f hf).symm))

/-- 概要：loop に送った点つき fiber の kernel fork も極限。
方針：円からの内部 Hom は右随伴なので kernel を保存する。
規約：零射の保存も右随伴性から得る。
使われ方：Goerss–Jardine I §7、HA §1.4.2。loop と fiber の厳密な比較。 -/
def loopFiberKernelIsLimit {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    IsLimit ((pointedFiberKernelFork p).map (ihom PointedSimplicialSet.circle.{u})) :=
  (pointedFiberKernelFork p).mapIsLimit (pointedFiberKernelIsLimit p)
    (ihom PointedSimplicialSet.circle.{u})

/-- 概要：fiber の loop と loop による射の fiber は点つき同型。
方針：二つの kernel fork の極限の一意性を使う。
規約：Kan 性を要求せず実際の点つき同型を構成する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。fiber の随伴構造射の比較。 -/
def loopPointedFiberIso {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pointedFiber p) ≅
      pointedFiber (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p) :=
  (loopFiberKernelIsLimit p).conePointUniqueUpToIso
    (pointedFiberKernelIsLimit (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p))

/-- 概要：loop と fiber の同型は全空間への包含と可換。
方針：極限の一意同型の円錐射の計算を使う。
規約：右辺は包含を loop に送った点つき射。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber の Ω 条件の可換正方形。 -/
@[reassoc (attr := simp)]
theorem loopPointedFiberIso_hom_ι {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    (loopPointedFiberIso p).hom ≫
      pointedFiberι (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p) =
        PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pointedFiberι p) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end

end SerrePositivity.KST.Spectra
