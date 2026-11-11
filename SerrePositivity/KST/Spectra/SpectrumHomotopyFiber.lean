module

public import SerrePositivity.KST.Spectra.SpectrumFibrationReplacement
public import SerrePositivity.KST.Spectra.SpectrumFibrationSequence

/-!
概要：任意の Ω スペクトルの射の homotopy fiber と全整数次数の長完全列。
方針：mapping path と単射置換で段ごとの fibration に直し、比較同型で完全性を移す。
規約：fiber は BF 対象。Sp の ∞ 極限との比較は γ3 後に扱う。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、HTT A.3.3、HA §1.4.2。KST の fiber 列。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：任意の Ω スペクトルの射の homotopy fiber。
方針：段ごとの fibration 置換の fiber を取り、構造射を単射置換する。
規約：Sp の対象であるが ∞ 極限であることはまだ主張しない。
使われ方：BF 1978 §2、HA §1.4.2。任意の射の長完全列の対象。 -/
def homotopyFiber {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : OmegaSpectrum.{u} :=
  fiber (fibrationReplacementProjection f) inferInstance

/-- 概要：任意の射の homotopy fiber から元の源への厳密な射。
方針：置換後の fiber 包含と元の源への射影を合成する。
規約：fiber の単射置換も含む構成。
使われ方：BF 1978 §2、HA §1.4.2。長完全列の包含の誘導準同型。 -/
def homotopyFiberInclusion {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : homotopyFiber f ⟶ X :=
  fiberInclusion (fibrationReplacementProjection f) inferInstance ≫ fibrationReplacementRetraction f

/-- 概要：任意の射の homotopy fiber 列の連結準同型。
方針：実際の fibration 置換の整数次数の連結準同型を使う。
規約：π_(j+1)(Y) から π_j(homotopyFiber f) への群準同型。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。任意の射の長完全列。 -/
def homotopyFiberBoundary {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    homotopyGroup Y (j + 1) →* homotopyGroup (homotopyFiber f) j :=
  stableConnectingHom (fibrationReplacementProjection f) j

/-- 概要：元の源と fibration 置換の中間対象の整数次数群の比較同型。
方針：比較射の全単射な誘導準同型を群同型へ束ねる。
規約：順写像は元の比較射の誘導準同型そのもの。
使われ方：BF 1978 §2、HA §1.4.2。長完全列の完全性の移送。 -/
def fibrationReplacementGroupEquiv {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    homotopyGroup X j ≃* homotopyGroup (fibrationReplacement f) j :=
  (fibrationReplacementUnit_piIsomorphism f).groupEquiv j

/-- 概要：比較同型は元の源への fiber 包含を置換後の包含へ移す。
方針：誘導準同型の合成式と比較射・射影の右逆性を使う。
規約：全整数次数。
使われ方：BF 1978 §2、HA §1.4.2。fiber と全空間の完全性の移送。 -/
theorem fibrationReplacementGroupEquiv_inclusion {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup (homotopyFiber f) j) :
    fibrationReplacementGroupEquiv f j (homotopyMap (homotopyFiberInclusion f) j a) =
      homotopyMap (fiberInclusion (fibrationReplacementProjection f) inferInstance) j a := by
  change homotopyMap (fibrationReplacementUnit f) j
    (homotopyMap (fiberInclusion (fibrationReplacementProjection f) inferInstance ≫
      fibrationReplacementRetraction f) j a) = _
  rw [homotopyMap_comp, MonoidHom.comp_apply, fibrationReplacementUnit_retraction_map]

/-- 概要：任意の射の fiber 包含の核は連結準同型の像。
方針：fibration 置換の fiber の位置の完全性を比較群同型で移す。
規約：全整数次数で有効。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。長完全列の fiber の位置。 -/
theorem homotopy_exact_connecting_fiber {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup (homotopyFiber f) j) :
    homotopyMap (homotopyFiberInclusion f) j a = 1 ↔
      ∃ b : homotopyGroup Y (j + 1), homotopyFiberBoundary f j b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (homotopyFiberBoundary f j)
    (homotopyMap (homotopyFiberInclusion f) j)
    (stableConnectingHom (fibrationReplacementProjection f) j)
    (homotopyMap (fiberInclusion (fibrationReplacementProjection f) inferInstance) j)
    (MulEquiv.refl _) (MulEquiv.refl _) (fibrationReplacementGroupEquiv f j)
    (fun _ ↦ rfl) (fibrationReplacementGroupEquiv_inclusion f j)
    (stable_exact_connecting_fiber (fibrationReplacementProjection f) j) a

/-- 概要：任意の射の連結準同型の核は元の源からの誘導準同型の像。
方針：fibration 置換の底の位置の完全性を厳密な因子分解で移す。
規約：元の射 f の誘導準同型を使う。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。長完全列の底の位置。 -/
theorem homotopy_exact_total_base {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup Y (j + 1)) :
    homotopyFiberBoundary f j a = 1 ↔
      ∃ b : homotopyGroup X (j + 1), homotopyMap f (j + 1) b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (homotopyMap f (j + 1)) (homotopyFiberBoundary f j)
    (homotopyMap (fibrationReplacementProjection f) (j + 1))
    (stableConnectingHom (fibrationReplacementProjection f) j)
    (fibrationReplacementGroupEquiv f (j + 1)) (MulEquiv.refl _) (MulEquiv.refl _)
    (fun b ↦ (fibrationReplacement_projection_map f (j + 1) b).symm) (fun _ ↦ rfl)
    (stable_exact_total_base (fibrationReplacementProjection f) j) a

/-- 概要：任意の射の誘導準同型の核は homotopy fiber の包含の像。
方針：fibration 置換の全空間の位置の完全性を二つの可換式で移す。
規約：全整数次数で元の射 f の核を計算する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。長完全列の全空間の位置。 -/
theorem homotopy_exact_fiber_total {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup X j) :
    homotopyMap f j a = 1 ↔
      ∃ b : homotopyGroup (homotopyFiber f) j, homotopyMap (homotopyFiberInclusion f) j b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (homotopyMap (homotopyFiberInclusion f) j) (homotopyMap f j)
    (homotopyMap (fiberInclusion (fibrationReplacementProjection f) inferInstance) j)
    (homotopyMap (fibrationReplacementProjection f) j)
    (MulEquiv.refl _) (fibrationReplacementGroupEquiv f j) (MulEquiv.refl _)
    (fibrationReplacementGroupEquiv_inclusion f j)
    (fun b ↦ (fibrationReplacement_projection_map f j b).symm)
    (stable_exact_fiber_total (fibrationReplacementProjection f) j) a

/-- 概要：任意の Ω スペクトルの射の homotopy fiber 列は全整数次数で長完全列を与える。
方針：fiber・全空間・底の三つの位置の完全性を束ねる。
規約：元の射への fibration 仮定は不要。∞ 極限との比較は含めない。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、HA §1.4.2。KST の全次数の fiber 完全列。 -/
theorem homotopyFiberLongExact {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    (∀ (j : ℤ) (a : homotopyGroup (homotopyFiber f) j),
      homotopyMap (homotopyFiberInclusion f) j a = 1 ↔
        ∃ b : homotopyGroup Y (j + 1), homotopyFiberBoundary f j b = a) ∧
    (∀ (j : ℤ) (a : homotopyGroup X j), homotopyMap f j a = 1 ↔
      ∃ b : homotopyGroup (homotopyFiber f) j, homotopyMap (homotopyFiberInclusion f) j b = a) ∧
    (∀ (j : ℤ) (a : homotopyGroup Y (j + 1)), homotopyFiberBoundary f j a = 1 ↔
      ∃ b : homotopyGroup X (j + 1), homotopyMap f (j + 1) b = a) :=
  ⟨homotopy_exact_connecting_fiber f, homotopy_exact_fiber_total f, homotopy_exact_total_base f⟩

/-- 概要：任意の射の連結準同型と fiber 包含の誘導準同型の合成は自明。
方針：fiber の位置の完全性に連結準同型の像を入れる。
規約：乗法記法で単位元への定数写像。
使われ方：Goerss–Jardine I §7、HA §1.4.2。長完全列の隣接射。 -/
theorem homotopyFiberBoundary_inclusion {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup Y (j + 1)) :
    homotopyMap (homotopyFiberInclusion f) j (homotopyFiberBoundary f j a) = 1 :=
  (homotopy_exact_connecting_fiber f j _).2 ⟨a, rfl⟩

/-- 概要：任意の射の fiber 包含と元の射の誘導準同型の合成は自明。
方針：全空間の位置の完全性に包含の像を入れる。
規約：全整数次数のホモトピー群上の主張。
使われ方：Goerss–Jardine I §7、HA §1.4.2。fiber 列の零合成。 -/
theorem homotopyFiberInclusion_projection {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup (homotopyFiber f) j) :
    homotopyMap f j (homotopyMap (homotopyFiberInclusion f) j a) = 1 :=
  (homotopy_exact_fiber_total f j _).2 ⟨a, rfl⟩

/-- 概要：任意の射の誘導準同型と連結準同型の合成は自明。
方針：底の位置の完全性に元の射の像を入れる。
規約：連結準同型は一つ下の整数次数へ移る。
使われ方：Goerss–Jardine I §7、HA §1.4.2。長完全列の隣接射。 -/
theorem homotopyFiberBoundary_projection {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup X (j + 1)) :
    homotopyFiberBoundary f j (homotopyMap f (j + 1) a) = 1 :=
  (homotopy_exact_total_base f j _).2 ⟨a, rfl⟩

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
