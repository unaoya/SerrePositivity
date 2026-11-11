module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitMap
public import SerrePositivity.KST.Spectra.PointedComponentCancellation
public import SerrePositivity.KST.Spectra.ComponentHomotopyMaps

/-!
概要：BF homotopy end への標準比較と係数の射への作用の自然性。
方針：標的の全単射 RLP 射影へ合成し、置換前の定数族の厳密な可換式で比較する。
規約：各段の成分と全整数次数の誘導準同型で自然性を述べる。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。hG の標準射の自然性。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet


namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {D E : I ⥤ OmegaSpectrum.{u}}

/-- 概要：BF homotopy end の射は段ごとの Kan end の射へ射影される。
方針：Kan Ω 列の図式からの持ち上げの計算式を使う。
規約：各段の点つき射の厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。自然性を置換前で検査する。 -/
theorem homotopyLimitMap_projection (τ : D ⟶ E) (n : ℕ) :
    (homotopyLimitMap τ).app n ≫ (homotopyLimitProjection E).app n =
      (homotopyLimitProjection D).app n ≫
        (KanSequence.homotopyLimitMap (Functor.whiskerRight τ forgetToKan)).app n :=
  KanSequence.homotopyLimitSpectrumMap_projection
    (D := D ⋙ forgetToKan) (E := E ⋙ forgetToKan)
    (fun i ↦ (D.obj i).toKanSequence_omega) (fun i ↦ (E.obj i).toKanSequence_omega)
    (Functor.whiskerRight τ forgetToKan) n

/-- 概要：BF homotopy end への標準比較は錐の頂点と係数に関して各段の成分で自然。
方針：標的の比較へ合成した厳密な可換式を全単射 RLP で打ち消す。
規約：全ての射は実際の BF 射。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。hG への標準射の自然性。 -/
theorem homotopyLimitConeComparison_natural_component
    (c : Cone D) (d : Cone E) (f : c.pt ⟶ d.pt) (τ : D ⟶ E)
    (h : ∀ i, f ≫ d.π.app i = c.π.app i ≫ τ.app i) (n : ℕ) :
    PointedMapping.componentOf (f.app n ≫ (homotopyLimitConeComparison d).app n) =
      PointedMapping.componentOf ((homotopyLimitConeComparison c).app n ≫
        (homotopyLimitMap τ).app n) := by
  have hn := PointedWeightedEnd.coneComparison_natural (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (KanSequence.levelCone (forgetToKan.mapCone c) n)
    (KanSequence.levelCone (forgetToKan.mapCone d) n) (f.app n)
    (KanSequence.homotopyLimitLevelTransformation (Functor.whiskerRight τ forgetToKan) n)
    (fun i ↦ congrArg (fun g : c.pt ⟶ E.obj i ↦ g.app n) (h i))
  apply PointedMapping.componentOf_eq_of_comp_eq_rlp ((homotopyLimitProjection E).app n)
    (KanSequence.replacementStage (KanSequence.homotopyLimit (E ⋙ forgetToKan)) n).projection_rlp
  rw [Category.assoc, homotopyLimitConeComparison_projection, Category.assoc,
    homotopyLimitMap_projection, ← Category.assoc, homotopyLimitConeComparison_projection]
  exact hn

/-- 概要：BF end への標準比較は全整数次数の誘導準同型で自然。
方針：各段の成分での自然性をホモトピー不変性へ渡す。
規約：極限錐や ∞ 極限性を仮定しない。
使われ方：HA §1.4.2、BF 1978 §2。hG の単位の π_* の自然性。 -/
theorem homotopyLimitConeComparison_natural
    (c : Cone D) (d : Cone E) (f : c.pt ⟶ d.pt) (τ : D ⟶ E)
    (h : ∀ i, f ≫ d.π.app i = c.π.app i ≫ τ.app i) (j : ℤ) :
    homotopyMap (f ≫ homotopyLimitConeComparison d) j =
      homotopyMap (homotopyLimitConeComparison c ≫ homotopyLimitMap τ) j :=
  homotopyMap_eq_of_levelComponent (X := c.pt) (Y := homotopyLimit E)
    (f ≫ homotopyLimitConeComparison d) (homotopyLimitConeComparison c ≫ homotopyLimitMap τ)
    (homotopyLimitConeComparison_natural_component c d f τ h) j

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
