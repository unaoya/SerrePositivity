module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFaceExtension

/-!
概要：空の面を含む全ての面で一般解像と明示的な解像を同定する。
方針：非空の場合の同型と空の場合の始対象性を組み合わせ、包含との可換性で自然性を示す。
規約：選んだ同型の順方向は大きい解像への包含によって特徴づける。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の同型を有限の貼り合わせへ拡張する入力。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：任意の面の二つの解像の間に包含と可換な同型が存在する。
方針：非空の頂点集合を列挙し、空の場合は左随伴による始対象の保存を使う。
規約：存在する同型には包含との可換条件を添える。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の同型の一貫した選択。 -/
lemma exists_coherentResolutionFaceExtensionIso {n : ℕ} (T : Finset (Fin (n + 1))) :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.obj (stdSimplex.face T).toSSet ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).toSSet,
      e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (stdSimplex.face T).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌ := by
  classical
  by_cases hT : T.Nonempty
  · have hc : T.card = (T.card - 1) + 1 := by
      have hp := Finset.card_pos.mpr hT
      omega
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceExtensionIso T (T.orderIsoOfFin hc),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceExtensionIso_hom_ι T (T.orderIsoOfFin hc)⟩
  · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    have hS : IsInitial (stdSimplex.face.{u} (∅ : Finset (Fin (n + 1)))).toSSet := by
      rw [stdSimplex.face_empty]
      exact Subcomplex.isInitialBot
    have hQ : IsInitial (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace.{u} (∅ : Finset (Fin (n + 1)))).toSSet := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace_empty]
      exact Subcomplex.isInitialBot
    let h := hS.isInitialObj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution
    exact ⟨h.uniqueUpToIso hQ, h.hom_ext _ _⟩

/-- 概要：全ての面について選んだ一般解像と明示的な解像の同型。
方針：包含と可換な同型の存在から選ぶ。
規約：空の面を含む。順方向の射は包含との可換性により一意。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の図式の自然同型。 -/
noncomputable def coherentResolutionFaceExtensionIsoAll {n : ℕ} (T : Finset (Fin (n + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.obj (stdSimplex.face T).toSSet ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).toSSet :=
  Classical.choose (exists_coherentResolutionFaceExtensionIso T)

/-- 概要：選んだ面の同型は包含と可換。
方針：選択した同型の存在証明の条件を取り出す。
規約：順序同型の列挙には依存しない条件。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の同型の貼り合わせの可換式。 -/
lemma coherentResolutionFaceExtensionIsoAll_hom_ι {n : ℕ} (T : Finset (Fin (n + 1))) :
    (coherentResolutionFaceExtensionIsoAll.{u} T).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (stdSimplex.face T).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌ :=
  Classical.choose_spec (exists_coherentResolutionFaceExtensionIso T)

/-- 概要：全ての面の解像の同型は面の包含に自然。
方針：大きい解像への単射な包含の後で比較し、同じ包含を解像で写す式へ戻す。
規約：空の面からの包含も含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面と交わりの図式の自然同型。 -/
lemma coherentResolutionFaceExtensionIsoAll_naturality {n : ℕ}
    {T U : Finset (Fin (n + 1))} (h : T ⊆ U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.map (Subcomplex.homOfLE ((stdSimplex.face_le_face_iff T U).mpr h)) ≫
      (coherentResolutionFaceExtensionIsoAll U).hom =
      (coherentResolutionFaceExtensionIsoAll T).hom ≫
        Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace_mono h) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace U).ι).mp
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (stdSimplex.face T).ι ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso.hom.app ⦋n⦌ := by
      rw [Category.assoc, coherentResolutionFaceExtensionIsoAll_hom_ι,
        ← Category.assoc, ← CategoryTheory.Functor.map_comp, Subcomplex.homOfLE_ι]
    _ = _ := by
      rw [Category.assoc, Subcomplex.homOfLE_ι, coherentResolutionFaceExtensionIsoAll_hom_ι]

/-- 概要：全ての面の解像の同型は射影と可換。
方針：標準単体への包含の後で比較し、一般の射影の自然性を使う。
規約：空の面を含む同じ式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、貼り合わせ後の射影の同定。 -/
lemma coherentResolutionFaceExtensionIsoAll_projection {n : ℕ} (T : Finset (Fin (n + 1))) :
    (coherentResolutionFaceExtensionIsoAll.{u} T).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (stdSimplex.face T).toSSet := by
  apply (cancel_mono (stdSimplex.face T).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection_ι, ← Category.assoc,
    coherentResolutionFaceExtensionIsoAll_hom_ι, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionStdIso_hom_projection]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality (stdSimplex.face T).ι

/-- 概要：全ての面の包含は一般解像を適用しても単射。
方針：面の同型で明示的な解像の単射な包含へ比較する。
規約：空の面も含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の包含の単射性への入力。 -/
lemma coherentResolution_map_face_ι_mono_all {n : ℕ} (T : Finset (Fin (n + 1))) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.{u}.map (stdSimplex.face T).ι) := by
  haveI : Mono ((coherentResolutionFaceExtensionIsoAll.{u} T).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι) := inferInstance
  exact mono_of_mono_fac (coherentResolutionFaceExtensionIsoAll_hom_ι T).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
