module

public import SerrePositivity.KST.Spectra.MappingKanSequence
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence

/-!
概要：点つき内部 Hom を各段へ施した Kan 列の Ω 条件。
方針：随伴構造射を内部 Hom の二つの源の交換同型で計算し、π_* 同型の保存を使う。
規約：単射性は最後に BF 置換で回復する。∞ 極限の主張を含めない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。有理化と後続の Tot の構成材料。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace KanSequence

/-- 概要：内部 Hom の列の随伴構造射は、元の随伴構造射の Hom と源交換の合成。
方針：テンソル交換の curry の一般式を点つき単体集合へ適用する。
規約：構造射の厳密な等式。
使われ方：BF 1978 §2、HA §1.4.2。Ω 条件を写像空間へ移す。 -/
theorem mapping_adjoint (A : PointedSimplicialSet.{u}) (X : KanSequence.{u}) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((mapping A X).level n).space ((mapping A X).level (n + 1)).space)
      ((mapping A X).sigma n) =
    (ihom A).map ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space) (X.sigma n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A PointedSimplicialSet.circle.{u} (X.level (n + 1)).space).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.curry_strength PointedSimplicialSet.circle.{u} A
    (X.level n).space (X.level (n + 1)).space (X.sigma n)

/-- 概要：Ω 条件は任意の点つき源からの内部 Hom の列で保存される。
方針：標的変数の π_* 同型保存と二つの内部 Hom の交換同型を合成する。
規約：源 A に Kan 性や有限性を仮定しない。
使われ方：BF 1978 §2、HA §1.4.2。cotensor の BF 対象の構成。 -/
theorem mapping_omegaCondition (A : PointedSimplicialSet.{u}) (X : KanSequence.{u})
    (hX : X.OmegaCondition) : (mapping A X).OmegaCondition := by
  intro n
  let f := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space) (X.sigma n)
  have hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (PointedObject.basedHomMap A f).right :=
    PointedMapping.post_piIsomorphism A f (hX n)
  let e := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A PointedSimplicialSet.circle.{u} (X.level (n + 1)).space
  let e' : (PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (n + 1)).space)).right ≅
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.basedHom A (X.level (n + 1)).space)).right :=
    PointedSimplicialSet.forget.mapIso e
  have he : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e'.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e'
  have h := hf.comp he
  have hformula := congrArg Under.Hom.right (mapping_adjoint A X n)
  change _ = (PointedObject.basedHomMap A f).right ≫ e'.hom at hformula
  rw [← hformula] at h
  exact h

end KanSequence

namespace OmegaSpectrum

/-- 概要：Ω スペクトルの各段に内部 Hom を施して得る BF 対象。
方針：内部 Hom の Kan Ω 列を単射置換する。
規約：導来 cotensor の ∞ 普遍性を主張しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。有理化と Tot の実構成。 -/
def cotensor (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  (KanSequence.mapping A X.toKanSequence).cofibrantOmegaSpectrum
    (KanSequence.mapping_omegaCondition A X.toKanSequence X.toKanSequence_omega)

/-- 概要：cotensor の BF 対象から実際の内部 Hom の Kan 列への比較。
方針：単射置換の標準比較射を使う。
規約：各段で全単射への RLP を持つ。
使われ方：BF 1978 §2、HA §1.4.2。cotensor の段の π_* 比較。 -/
def cotensorProjection (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) :
    KanSequence.Hom (cotensor A X).toKanSequence (KanSequence.mapping A X.toKanSequence) :=
  (KanSequence.mapping A X.toKanSequence).cofibrantOmegaProjection
    (KanSequence.mapping_omegaCondition A X.toKanSequence X.toKanSequence_omega)

/-- 概要：cotensor の比較射は各段で全ての単射への RLP を持つ。
方針：Kan 列の境界 cell 分解の比較射の性質を取り出す。
規約：任意の点つき源 A。
使われ方：BF 1978 §2、HTT A.3.3。cotensor の厳密な比較射の持ち上げ。 -/
theorem cotensorProjection_rlp (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((cotensorProjection A X).app n).right :=
  (KanSequence.replacementStage (KanSequence.mapping A X.toKanSequence) n).projection_rlp

/-- 概要：cotensor の比較射は各段で全基点 π_* 同型。
方針：全単射への RLP からの構成済みの比較を使う。
規約：零次数を含む。
使われ方：BF 1978 §2、HA §1.4.2。cotensor の整数次数群の計算。 -/
theorem cotensorProjection_piIsomorphism (A : PointedSimplicialSet.{u})
    (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((cotensorProjection A X).app n).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (cotensorProjection_rlp A X n)

end OmegaSpectrum

end

end SerrePositivity.KST.Spectra
