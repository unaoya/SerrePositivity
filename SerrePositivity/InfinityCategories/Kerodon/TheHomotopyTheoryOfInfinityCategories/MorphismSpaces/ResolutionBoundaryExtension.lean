module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionExtensionGluing

/-!
概要：標準単体の境界への一般解像は明示的な旗の境界と同型。
方針：面族の濃度による強い帰納法で同型を貼り合わせ、境界を覆う面族へ適用する。
規約：同型は大きい単体への包含と射影の両方に整合する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界に関する相対比較と解像の単射保存。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：空の面族の和で一般解像と明示的な解像を同定できる。
方針：空の和を空の頂点集合の面と同定する。
規約：同型の貼り合わせの帰納法の基底。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の有限和の比較。 -/
lemma hasCoherentResolutionExtension_faceUnion_empty (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion (∅ : Finset (Finset (Fin (n + 1))))) := by
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) =
      stdSimplex.face ∅ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion_empty, stdSimplex.face_empty]
  have hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace ∅ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_empty, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace_empty]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.hasCoherentResolutionExtension_congr hA hB).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.hasCoherentResolutionExtension_face ∅)

/-- 概要：面を一枚加えた有限和で解像を同定できる。
方針：和の残りと交わりの同型を使い、pushout の同型を貼り合わせる。
規約：交わりは各頂点集合と T の交わりの面族で表す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、同型の貼り合わせの帰納段階。 -/
lemma hasCoherentResolutionExtension_faceUnion_insert {n : ℕ}
    (S : Finset (Finset (Fin (n + 1)))) (T : Finset (Fin (n + 1)))
    (eS : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion S))
    (eI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} (S.image (fun U ↦ U ∩ T)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion (S.image (fun U ↦ U ∩ T)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} (insert T S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion (insert T S)) := by
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} S ⊓ stdSimplex.face T)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion S ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.hasCoherentResolutionExtension_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion_inf_face S T)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_inf_face S T)).mpr eI
  have hU := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.hasCoherentResolutionExtension_sup (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion S) (stdSimplex.face T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T) hI eS
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.hasCoherentResolutionExtension_face T)
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} S ⊔ stdSimplex.face T = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion (insert T S) :=
    (sup_comm _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion_insert T S).symm
  have hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion.{u} S ⊔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion (insert T S) :=
    (sup_comm _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_insert T S).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.hasCoherentResolutionExtension_congr hA hB).mp hU

/-- 概要：有限個の面の和で一般解像と明示的な解像を同定できる。
方針：面族の濃度による強い帰納法で、交わりの面族も小さくなることを使う。
規約：面族の空性や面の非空性を仮定しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の二つの解像の同定。 -/
lemma hasCoherentResolutionExtension_faceUnion {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion S) := by
  classical
  have go : ∀ k, ∀ R : Finset (Finset (Fin (n + 1))), R.card = k →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} R)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion R) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R hk
      by_cases hR : R = ∅
      · subst R
        exact hasCoherentResolutionExtension_faceUnion_empty n
      · obtain ⟨T, hT⟩ := Finset.nonempty_iff_ne_empty.mpr hR
        have hsmall : (R.erase T).card < k := by
          rw [← hk]
          exact Finset.card_erase_lt_of_mem hT
        have hinter : ((R.erase T).image (fun U ↦ U ∩ T)).card < k :=
          lt_of_le_of_lt Finset.card_image_le hsmall
        have eS := ih (R.erase T).card hsmall (R.erase T) rfl
        have eI := ih ((R.erase T).image (fun U ↦ U ∩ T)).card hinter
          ((R.erase T).image (fun U ↦ U ∩ T)) rfl
        have e := hasCoherentResolutionExtension_faceUnion_insert (R.erase T) T eS eI
        exact Eq.mp (congrArg (fun Q : Finset (Finset (Fin (n + 1))) ↦
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} Q)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion Q)) (Finset.insert_erase hT)) e
  exact go S.card S rfl

/-- 概要：境界で一般解像と明示的な解像を包含と可換に同定できる。
方針：境界を覆う全ての余次元一の面の族を使う。
規約：零単体の境界を含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界上の一般の射影の比較。 -/
lemma hasCoherentResolutionExtension_boundary (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HasCoherentResolutionExtension (SSet.boundary.{u} n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundary n) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.hasCoherentResolutionExtension_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion_boundaryFaces n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_boundaryFaces n)).mp
      (hasCoherentResolutionExtension_faceUnion (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundaryFaces n))

/-- 概要：境界への一般解像と明示的な旗の境界の同型。
方針：包含と可換な同型の存在から選ぶ。
規約：順方向の射は境界の包含との可換性で一意に決まる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、明示的な境界を一般の解像と結ぶ。 -/
noncomputable def coherentResolutionBoundaryExtensionIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.obj (SSet.boundary n).toSSet ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundary n).toSSet :=
  Classical.choose (hasCoherentResolutionExtension_boundary n)

/-- 概要：境界の同型は大きい単体の解像への包含と可換。
方針：選んだ同型の条件を取り出す。
規約：標準単体での解像の回収同型を後に合成する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の包含の単射性と相対比較。 -/
lemma coherentResolutionBoundaryExtensionIso_hom_ι (n : ℕ) :
    (coherentResolutionBoundaryExtensionIso.{u} n).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundary n).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (SSet.boundary n).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌ :=
  Classical.choose_spec (hasCoherentResolutionExtension_boundary n)

/-- 概要：境界の同型は一般の射影と明示的な境界の射影を結ぶ。
方針：境界の包含の後で比較し、一般の射影の自然性を使う。
規約：境界を覆う面族の選択は結果の式に現れない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界上の射影の同値性の移送。 -/
lemma coherentResolutionBoundaryExtensionIso_projection (n : ℕ) :
    (coherentResolutionBoundaryExtensionIso.{u} n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundaryProjection n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (SSet.boundary n).toSSet := by
  apply (cancel_mono (SSet.boundary n).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundaryProjection_ι, ← Category.assoc,
    coherentResolutionBoundaryExtensionIso_hom_ι, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso_hom_projection]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality (SSet.boundary n).ι

/-- 概要：標準単体の境界上の一般の解像の射影は前合成による同値。
方針：境界の回収同型の後に明示的な境界の射影を合成する。
規約：全ての次数の境界で成立する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、相対拡張に必要な境界上の比較。 -/
lemma coherentResolutionProjectionAll_boundary_isPrecompositionEquivalence (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.{u}.app (SSet.boundary n).toSSet) := by
  rw [← coherentResolutionBoundaryExtensionIso_projection]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (coherentResolutionBoundaryExtensionIso n)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundaryProjection_isPrecompositionEquivalence n)

/-- 概要：境界の包含に一般解像を適用した射は単射。
方針：境界の回収同型で明示的な境界の単射な包含へ比較する。
規約：次数零の空の境界も含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、一般の解像の単射保存の生成元。 -/
lemma coherentResolution_map_boundary_ι_mono (n : ℕ) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.map (SSet.boundary n).ι) := by
  haveI : Mono ((coherentResolutionBoundaryExtensionIso.{u} n).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundary n).ι) := inferInstance
  exact mono_of_mono_fac (coherentResolutionBoundaryExtensionIso_hom_ι n).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
