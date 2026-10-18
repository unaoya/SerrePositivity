module

public import SerrePositivity.KST.Spectra.CotensorPower
public import SerrePositivity.KST.Spectra.RationalTelescopeCoefficients
public import SerrePositivity.KST.Spectra.FilteredSpectrumInjection
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：円の次数射から構成する実際の BF スペクトルの有理 telescope 図式。
方針：2,3,4,… の次数射の前合成を順に並べ、全整数次数の遷移を計算する。
規約：源の圏は universe を合わせた AsSmall ℕ。
使われ方：BF 1978 §2、HA §1.4.2。スペクトルの有理化の実構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：円の次数 2,3,4,… の前合成を BF cotensor の自己射として並べた図式。
方針：隣接射から自然数の圏の関手を作る。
規約：各段は同じ BF cotensor、長い射は厳密な合成。
使われ方：BF 1978 §2、HA §1.4.2。有理 telescope の自然数の図式。 -/
def rationalSequence (X : OmegaSpectrum.{u}) : ℕ ⥤ OmegaSpectrum.{u} :=
  Functor.ofSequence (X := fun _ : ℕ => cotensor CirclePower.space.{u} X)
    (fun n => cotensorPre (CirclePower.powerMap (n + 2)) X)

/-- 概要：自然数の有理化図式の遷移は整数次数の群で区間係数の冪。
方針：隣接射の冪作用と係数の合成則を自然数帰納法で合成する。
規約：i≤l、d は任意の整数次数。
使われ方：BF 1978 §2、HA §1.4.2。有理化の群の直極限の計算。 -/
theorem rationalSequence_homotopyMap (X : OmegaSpectrum.{u}) (d : ℤ)
    (i l : ℕ) (hil : i ≤ l) (a : homotopyGroup (cotensor CirclePower.space.{u} X) d) :
    homotopyMap ((rationalSequence X).map (homOfLE hil)) d a =
      a ^ RationalTelescope.coefficient i l := by
  induction l, hil using Nat.le_induction with
  | base =>
    have hf : (rationalSequence X).map (homOfLE (Nat.le_refl i)) =
        𝟙 (cotensor CirclePower.space.{u} X) := (rationalSequence X).map_id i
    calc
      _ = homotopyMap (𝟙 (cotensor CirclePower.space.{u} X)) d a :=
        congrArg (fun f : cotensor CirclePower.space.{u} X ⟶
          cotensor CirclePower.space X => homotopyMap f d a) hf
      _ = a := DFunLike.congr_fun (homotopyMap_id _ _) a
      _ = _ := by rw [RationalTelescope.coefficient_self, pow_one]
  | succ l hil ih =>
    have hs : (rationalSequence X).map (homOfLE (Nat.le_succ l)) =
        cotensorPre (CirclePower.powerMap (l + 2)) X :=
      Functor.ofSequence_map_homOfLE_succ _ l
    have hf : (rationalSequence X).map (homOfLE (Nat.le.step hil)) =
        (rationalSequence X).map (homOfLE hil) ≫
          cotensorPre (CirclePower.powerMap (l + 2)) X := by
      calc
        _ = (rationalSequence X).map (homOfLE hil ≫ homOfLE (Nat.le_succ l)) :=
          congrArg (rationalSequence X).map (Subsingleton.elim _ _)
        _ = _ := ((rationalSequence X).map_comp _ _).trans
          (congrArg (fun f => (rationalSequence X).map (homOfLE hil) ≫ f) hs)
    calc
      _ = homotopyMap ((rationalSequence X).map (homOfLE hil) ≫
          cotensorPre (CirclePower.powerMap (l + 2)) X) d a :=
        congrArg (fun f : cotensor CirclePower.space.{u} X ⟶
          cotensor CirclePower.space X => homotopyMap f d a) hf
      _ = homotopyMap (cotensorPre (CirclePower.powerMap (l + 2)) X) d
          (homotopyMap ((rationalSequence X).map (homOfLE hil)) d a) :=
        DFunLike.congr_fun (homotopyMap_comp _ _ _) a
      _ = (a ^ RationalTelescope.coefficient i l) ^ (l + 2) := by
        erw [cotensorPre_power_homotopyMap, ih]
      _ = _ := by
        rw [← pow_mul, RationalTelescope.coefficient_comp hil (Nat.le_succ l),
          RationalTelescope.coefficient_step, Nat.mul_comm]

/-- 概要：universe を揃えた有理化の filtered 図式。
方針：AsSmall の忘却を自然数の図式へ前合成する。
規約：対象と射の universe はともに u。
使われ方：BF 1978 §2、HA §1.4.2。実証済みの filtered Kan 余極限への入力。 -/
def rationalDiagram (X : OmegaSpectrum.{u}) : AsSmall.{u} ℕ ⥤ OmegaSpectrum.{u} :=
  AsSmall.down ⋙ rationalSequence X

/-- 概要：有理化の実際の filtered 図式の全整数次数の遷移の式。
方針：AsSmall の射を自然数の射へ戻し、区間係数の冪作用を使う。
規約：射の存在から自然数の順序を得る。
使われ方：BF 1978 §2、HA §1.4.2。π_* の群の cocone の自然性。 -/
theorem rationalDiagram_homotopyMap (X : OmegaSpectrum.{u}) (d : ℤ)
    {i l : AsSmall.{u} ℕ} (f : i ⟶ l)
    (a : homotopyGroup (cotensor CirclePower.space.{u} X) d) :
    homotopyMap ((rationalDiagram X).map f) d a =
      a ^ RationalTelescope.coefficient (AsSmall.down.obj i) (AsSmall.down.obj l) :=
  rationalSequence_homotopyMap X d (AsSmall.down.obj i) (AsSmall.down.obj l) (leOfHom f.down) a

/-- 概要：円の次数射の有理 telescope の BF 対象。
方針：各段で実際の Kan filtered 余極限を取り、cofibrant 置換する。
規約：loop による次数移動の補正は別に行う。
使われ方：BF 1978 §2、HA §1.4.2。スペクトルの有理化対象の元の telescope。 -/
def rationalLoopTelescope (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  filteredOmegaSpectrum (rationalDiagram X)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
