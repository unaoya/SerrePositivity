module

public import SerrePositivity.KST.Spectra.OriginalLoopModelNaturality
public import SerrePositivity.KST.Spectra.RawRationalInjection
public import SerrePositivity.KST.Spectra.InverseCompositeComponents

/-!
概要：有理化の実際の単位写像と実際の射への作用の自然性。
方針：関手的な Kan 図式の telescope へ射影し、随伴と零段注入の比較をつなぐ。
規約：各段の成分と全整数次数の誘導準同型で自然性を示す。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。有理化の標準射。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：有理化の射を関手的な図式へ戻すと自然変換からの射と同じ成分。
方針：標的の BF 比較の逆方向の射の右ホモトピー逆を使う。
規約：各段の点つき成分の等式。
使われ方：BF 1978 §2、HTT A.3.3。元の有理化対象での自然性の検査。 -/
theorem rationalizationMap_projection_component {X Y : OmegaSpectrum.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    PointedMapping.componentOf ((rationalizationMap f).app n ≫
      (rationalizationProjection Y).app n) =
    PointedMapping.componentOf ((rationalizationProjection X).app n ≫
      (tailMap (rawRationalLoopMap f)).app n) :=
  inverseComposite_projection_component
    (rationalizationProjection Y) (rationalizationProjection_levelwise Y)
    (rationalizationProjection X) (tailMap (rawRationalLoopMap f)) n

/-- 概要：有理化の単位は元のスペクトルの射に対して各段の成分で自然。
方針：関手的な telescope への全基点 π_* 同型を打ち消し、模型と零段注入の自然性を合成する。
規約：両辺は元のスペクトルから既存の有理化対象への実際の射。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。単位の自然性。 -/
theorem rationalizationUnit_natural_component {X Y : OmegaSpectrum.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    PointedMapping.componentOf (f.app n ≫ (rationalizationUnit Y).app n) =
    PointedMapping.componentOf ((rationalizationUnit X).app n ≫ (rationalizationMap f).app n) :=
  PointedMapping.compositeUnit_natural
    (f.app n) ((originalLoopModelMap X).app n) ((originalLoopModelMap Y).app n)
    ((cotensorPost CirclePower.space.{u} f).app (n + 1))
    ((filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0)).app (n + 1))
    ((filteredSpectrumInjection (rationalDiagram Y) (AsSmall.up.obj 0)).app (n + 1))
    ((rationalLoopProjection X).app (n + 1)) ((rationalLoopProjection Y).app (n + 1))
    ((rawRationalLoopMap f).app (n + 1)) ((rationalizationMap f).app n)
    (rationalizationProjection_levelwise Y n)
    (originalLoopModelMap_natural_component f n)
    (rationalLoopInjection_natural_component f (n + 1))
    (rationalizationMap_projection_component f n)

/-- 概要：有理化の単位は全整数次数の誘導準同型で自然。
方針：各段の成分での自然性をホモトピー不変性へ渡す。
規約：全ての写像は構成済みの実際の BF 射に由来する。
使われ方：BF 1978 §2、HA §1.4.2。π_* のテンソル表示に適合する自然な単位。 -/
theorem rationalizationUnit_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    homotopyMap (f ≫ rationalizationUnit Y) j =
      homotopyMap (rationalizationUnit X ≫ rationalizationMap f) j :=
  homotopyMap_eq_of_levelComponent (X := X) (Y := rationalization Y)
    (f ≫ rationalizationUnit Y) (rationalizationUnit X ≫ rationalizationMap f)
    (rationalizationUnit_natural_component f) j

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
