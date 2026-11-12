module

public import SerrePositivity.KST.Spectra.MappingOmegaSequence
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting

/-!
概要：cotensor の源の制限を BF 対象間の実際の射へ持ち上げる。
方針：内部 Hom の源の制限を単射置換の比較射へ厳密に持ち上げる。
規約：持ち上げの厳密な関手法則は要求しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。有理化用の自己射の実現。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cotensor の源の射が誘導する BF 対象間の厳密な反変射。
方針：cofibrant な源から、内部 Hom の制限を標的の比較射へ持ち上げる。
規約：源の射に単射性や Kan 性を要求しない。
使われ方：BF 1978 §2、HTT A.3.3。loop 変数の実際の自己射。 -/
def cotensorPre {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) (X : OmegaSpectrum.{u}) :
    cotensor B X ⟶ cotensor A X := by
  let f : KanSequence.Hom (cotensor B X).toKanSequence (cotensor A X).toKanSequence :=
    KanSequence.liftHom (X := (cotensor B X).toKanSequence)
      (W := (cotensor A X).toKanSequence) (Z := KanSequence.mapping A X.toKanSequence)
      (cotensor B X).sigma_mono (cotensorProjection A X) (cotensorProjection_rlp A X)
      ((cotensorProjection B X).comp (KanSequence.mappingPre i X.toKanSequence))
  exact { app := f.app, comm := f.comm }

/-- 概要：持ち上げた cotensor の源の制限は内部 Hom の実際の制限と整合する。
方針：列の厳密持ち上げの比較式を取り出す。
規約：各段の点つき射の等式。
使われ方：BF 1978 §2、HA §1.4.2。自己射の π_* の計算。 -/
theorem cotensorPre_comparison {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (X : OmegaSpectrum.{u}) (n : ℕ) :
    (cotensorPre i X).app n ≫ (cotensorProjection A X).app n =
      (cotensorProjection B X).app n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space :=
  KanSequence.liftHom_fac (X := (cotensor B X).toKanSequence)
    (W := (cotensor A X).toKanSequence) (Z := KanSequence.mapping A X.toKanSequence)
    (cotensor B X).sigma_mono (cotensorProjection A X) (cotensorProjection_rlp A X)
    ((cotensorProjection B X).comp (KanSequence.mappingPre i X.toKanSequence)) n

/-- 概要：源の anodyne 射による cotensor の制限は各段で全基点 π_* 同型。
方針：源の制限の全単射 RLP と二つの BF 比較射の同型性を合成して打ち消す。
規約：A と B の Kan 性は不要。
使われ方：Goerss–Jardine I §7、BF 1978 §2。円の Kan 置換を cotensor で比較する。 -/
theorem cotensorPre_levelwise_of_anodyne {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i.right) (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((cotensorPre i X).app n).right := by
  have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp i hi _)
  have hcomp := (cotensorProjection_piIsomorphism B X n).comp hp
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((cotensorProjection A X).app n).right) _
    (cotensorProjection_piIsomorphism A X n)
  have h := congrArg Under.Hom.right (cotensorPre_comparison i X n)
  change ((cotensorPre i X).app n).right ≫ ((cotensorProjection A X).app n).right =
    ((cotensorProjection B X).app n).right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space).right at h
  rw [h]
  exact hcomp

/-- 概要：源の anodyne 射による cotensor の制限は全整数次数の π_* 同型。
方針：各段の全基点の同型を整数次数へ移す。
規約：coherent nerve の同値との比較は γ3 後。
使われ方：BF 1978 §2、HA §1.4.2。cotensor の源の置換不変性。 -/
theorem cotensorPre_piIsomorphism_of_anodyne {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i.right) (X : OmegaSpectrum.{u}) : PiIsomorphism (cotensorPre i X) :=
  piIsomorphism_of_levelwise _ (cotensorPre_levelwise_of_anodyne i hi X)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
