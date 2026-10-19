module

public import SerrePositivity.KST.Comparison.LocalCoefficientMorphismProperty
public import SerrePositivity.KST.Comparison.LocalCoefficientHorn
public import SerrePositivity.KST.Comparison.OverHornGenerators

/-!
# anodyne map の全局所係数ホモロジー保存

概要：全ての anodyne map が標的上の任意の局所係数で同型を誘導することを証明する。
方針：基底上の horn の小対象構成と鎖複体の余極限・単射保存を使う。
規約：Weibel K-book IV.1.6。原典の位相的議論を slice のセル表示で実現する。
使われ方：plus のセル添付後の Kan 置換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

/--
概要：基底上の horn 包含の局所係数鎖写像は擬同型である。
方針：標準単体へ引き戻した係数で horn の計算を使う。
規約：係数の平坦性を要求しない。
使われ方：基底上のセル表示の生成射。
-/
theorem overHornMap_quasiIso {B : SSet.{u}} (L : LocalCoefficientSystem B)
    (n : ℕ) (k : Fin (n + 2)) (τ : (Δ[n + 1] : SSet.{u}) ⟶ B) :
    QuasiIso ((overLocalCoefficientChainsFunctor L).map (overHornMap n k τ)) := by
  have hmap : (overLocalCoefficientChainsFunctor L).map (overHornMap n k τ) =
      localCoefficientChainsMap (Λ[n + 1, k]).ι (pullbackLocalCoefficients τ L) := by
    change (normalizedMooreComplex _).map
      ((coefficientSimplicialFunctor _).map
          (overLocalCoefficientSourceIso L (overHornMap n k τ)).hom ≫
        localCoefficientSimplicialMap _ _) = _
    rw [show (overLocalCoefficientSourceIso L (overHornMap n k τ)).hom = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [hmap]
  exact localCoefficientHorn_quasiIso k _

/--
概要：基底上の horn 生成射は固定した局所係数で同型を誘導する。
方針：生成射の添字を取り出して horn の擬同型を適用する。
規約：全ての正次元 horn。
使われ方：余積への拡張。
-/
theorem overHornGenerators_le_localHomology {B : SSet.{u}} (L : LocalCoefficientSystem B) :
    overHornGenerators B ≤ overLocalHomologyEquivalences L := by
  rintro X Y f hf
  simp only [overHornGenerators, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨⟨k, τ⟩⟩⟩ := hf
  exact (overLocalHomologyEquivalences_iff L _).mpr (overHornMap_quasiIso L n k τ)

/--
概要：基底上の horn 生成射の台は単射である。
方針：実際の horn 包含の単射性を使う。
規約：射の性質の逆像による表現。
使われ方：余積の後の pushout の単射性。
-/
theorem overHornGenerators_le_underlyingMonomorphisms (B : SSet.{u}) :
    overHornGenerators B ≤ overUnderlyingMonomorphisms B := by
  rintro X Y f hf
  simp only [overHornGenerators, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨⟨k, τ⟩⟩⟩ := hf
  change Mono (Λ[n + 1, k]).ι
  infer_instance

/--
概要：基底上の horn の余積の pushout は局所係数ホモロジーを保存する。
方針：余積の単射性と擬同型性を使い、実際の鎖複体の pushout へ移す。
規約：全ての指定宇宙の余積。
使われ方：超限セル添付の各段階。
-/
theorem overHornCellAttachments_le_localHomology {B : SSet.{u}}
    (L : LocalCoefficientSystem B) :
    (MorphismProperty.coproducts.{u} (overHornGenerators B)).pushouts ≤
      overLocalHomologyEquivalences L := by
  have hmono : MorphismProperty.coproducts.{u} (overHornGenerators B) ≤
      overUnderlyingMonomorphisms B :=
    (MorphismProperty.coproducts_monotone (overHornGenerators_le_underlyingMonomorphisms B)).trans
      (MorphismProperty.coproducts_le _)
  have hhom : MorphismProperty.coproducts.{u} (overHornGenerators B) ≤
      overLocalHomologyEquivalences L :=
    (MorphismProperty.coproducts_monotone (overHornGenerators_le_localHomology L)).trans
      (MorphismProperty.coproducts_le _)
  rintro X Y f ⟨A, C, p, l, r, hp, sq⟩
  have : Mono p.left := hmono p hp
  have : Mono p := Over.mono_of_mono_left _
  exact (overLocalHomologyEquivalences_iff L f).mpr
    (integralChain_quasiIso_of_pushout (sq.flip.map (overLocalCoefficientChainsFunctor L))
      ((overLocalHomologyEquivalences_iff L p).mp (hhom p hp)))

/--
概要：台が anodyne な基底上の射は局所係数ホモロジーを保存する。
方針：実際の slice の小対象構成と超限合成・retract の閉性を使う。
規約：基底の任意の局所係数系。
使われ方：通常の単体写像の全局所係数比較。
-/
theorem overLocalHomologyEquivalence_of_anodyne {B : SSet.{u}}
    (L : LocalCoefficientSystem B) {X Y : Over B} (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f.left) : overLocalHomologyEquivalences L f := by
  have hcell := overHornGenerators_cellPresentation f hf
  apply (show (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (overHornGenerators B)).pushouts).retracts ≤
      overLocalHomologyEquivalences L from ?_) f hcell
  rw [MorphismProperty.retracts_le_iff, MorphismProperty.transfiniteCompositions_le_iff]
  exact overHornCellAttachments_le_localHomology L

/--
概要：anodyne map は標的上の全ての局所係数ホモロジーで同型を誘導する。
方針：標的自身を基底として基底上の擬同型の定理を適用する。
規約：整数係数だけの条件より強い全局所係数の条件。
使われ方：Kan 置換後も plus の acyclic 性を保つ。
-/
theorem localHomologyIsomorphism_of_anodyne {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f) : LocalHomologyIsomorphism f := by
  intro L n
  let p : Over.mk f ⟶ Over.mk (𝟙 Y) := Over.homMk f (Category.comp_id f)
  have hp := overLocalHomologyEquivalence_of_anodyne L p hf
  have hm : (overLocalCoefficientChainsFunctor L).map p = localCoefficientChainsMap f L := by
    change (normalizedMooreComplex _).map
      ((coefficientSimplicialFunctor _).map (overLocalCoefficientSourceIso L p).hom ≫
        localCoefficientSimplicialMap _ _) = _
    rw [show (overLocalCoefficientSourceIso L p).hom = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have : QuasiIso (localCoefficientChainsMap f L) := by
    rw [← hm]
    exact (overLocalHomologyEquivalences_iff L p).mp hp
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

end SerrePositivity.KST.Comparison
