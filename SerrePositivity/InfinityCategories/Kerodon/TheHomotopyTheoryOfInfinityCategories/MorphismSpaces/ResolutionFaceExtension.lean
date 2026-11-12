module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionBoundaryProjection

/-!
概要：非空な面への左 Kan 拡張と明示的な旗の面の同定。
方針：面の標準単体による表示、解像の標準単体での回収、旗の面の表示を合成する。
規約：通常の単体集合の圏の余極限だけを使う。𝒮 と Cat_∞ の余極限は主張しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、一般の解像と明示的な境界を同定する準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：旗の解像の関手は左随伴。
方針：Yoneda に沿う左 Kan 拡張の構成済みの随伴を使う。
規約：通常の圏としての随伴である。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の余極限表示を解像で写す。 -/
instance coherentResolution_isLeftAdjoint : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.IsLeftAdjoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.isLeftAdjoint

/-- 概要：旗の解像は通常の単体集合の圏の余極限を保存する。
方針：左随伴による余極限保存を適用する。
規約：指定した大きさの図式についての保存条件。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の貼り合わせと左 Kan 拡張の整合性。 -/
instance coherentResolution_preservesColimitsOfSize :
    PreservesColimitsOfSize.{v, w} _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.leftAdjoint_preservesColimits

/-- 概要：面への解像関手の適用は明示的な旗の面と同型。
方針：面を標準単体へ戻し、標準単体で解像を回収して旗の面へ写す。
規約：頂点集合 T の順序同型の表示を明示的に受け取る。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、明示的な面と一般の解像の対応。 -/
noncomputable def coherentResolutionFaceExtensionIso {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.obj (stdSimplex.face T).toSSet ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).toSSet :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.mapIso
      (stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy T m e)).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.app ⦋m⦌ ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceIso T e

/-- 概要：面の同型は大きい単体の解像への包含と可換。
方針：小さい標準単体で前合成して、解像の標準単体での回収の自然性を使う。
規約：明示的な面の包含と、通常の面の包含を解像で写したものを比較する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の同型を貼り合わせるための可換式。 -/
lemma coherentResolutionFaceExtensionIso_hom_ι {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    (coherentResolutionFaceExtensionIso.{u} T e).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (stdSimplex.face T).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌ := by
  let s := stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy T m e)
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map s.hom)).mp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map s.hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map s.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋m⦌ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceIso T e).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι = _
  rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp, s.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceIso_hom_ι]
  have hs : s.hom ≫ (stdSimplex.face T).ι = SSet.stdSimplex.map (SimplexCategory.mkHom
      ((OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom)) := rfl
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hs]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.naturality (SimplexCategory.mkHom
    ((OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom))).symm

/-- 概要：標準単体での解像の回収同型は一般の射影と最大元の射影を結ぶ。
方針：逆向きの回収式に回収同型の順方向を前合成する。
規約：大きい標準単体の上の射の等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面上の同型と射影の比較。 -/
lemma coherentResolutionStdIso_hom_projection (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.{u}.hom.app ⦋n⦌ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Δ[n] := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.inv.app ⦋n⦌ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Δ[n] := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_std]
    _ = _ := Iso.hom_inv_id_assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.app ⦋n⦌) _

/-- 概要：面の解像の同型を通る射影は一般の解像の射影と一致する。
方針：標的の面の包含の後で比較し、包含との可換性と射影の自然性を使う。
規約：面をどの順序同型で表示しても同じ制限された射影になる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界上の射影を左 Kan 拡張の射影と同定する。 -/
lemma coherentResolutionFaceExtensionIso_projection {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    (coherentResolutionFaceExtensionIso.{u} T e).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (stdSimplex.face T).toSSet := by
  apply (cancel_mono (stdSimplex.face T).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection_ι, ← Category.assoc,
    coherentResolutionFaceExtensionIso_hom_ι, Category.assoc,
    coherentResolutionStdIso_hom_projection]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality (stdSimplex.face T).ι

/-- 概要：通常の面の包含は解像関手を適用しても単射。
方針：面の回収同型で、明示的な旗の面の単射な包含へ比較する。
規約：頂点集合が標準単体で表示される非空の場合。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の包含の単射性の面ごとの入力。 -/
lemma coherentResolution_map_face_ι_mono {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.map (stdSimplex.face T).ι) := by
  haveI : Mono ((coherentResolutionFaceExtensionIso.{u} T e).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι) := inferInstance
  exact mono_of_mono_fac (coherentResolutionFaceExtensionIso_hom_ι T e).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
