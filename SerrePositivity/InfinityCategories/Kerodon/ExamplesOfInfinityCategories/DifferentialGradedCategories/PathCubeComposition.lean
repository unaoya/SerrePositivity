module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathCubeDeletion

/-!
# Path の立方体の座標1面と区間での合成

概要：内部点を含む面の Path は、その点の前後の区間に制限した二つの Path の合成である。
方針：内部点を常に挿入し、選択した点を切断点の左右へ分けて和集合を回収する。
規約：Path の通常順の合成は前半の後に後半を進む。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の合成面の幾何学的な同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening
open scoped _root_.Simplicial
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：選んだ有限内部点を別の開区間に制限して Path を作る。
方針：新しい区間にある選択点を残し、新しい両端点を加える。
規約：新しい区間の端点に一致する選択点は内部点から除く。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面の左右の Path への制限。 -/
def pathCubeIntervalFunctor {c d : J} (hcd : c < d) (S : Finset (Set.Ioo a b)) :
    Set ↥S ⥤ Path c d :=
  (show Monotone (fun U : Set ↥S ↦ {z : Set.Ioo c d | ∃ t : S, t ∈ U ∧ t.val.val = z.val})
    from fun _ _ h _ ⟨t, ht, he⟩ ↦ ⟨t, h ht, he⟩).functor ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInteriorFunctor hcd

/-- 概要：選んだ内部点を常に含める操作を部分集合の関手にする。
方針：一つの点の挿入は包含を保つ。
規約：既に点を含む集合には同じ点を重ねて加えない。
使われ方：HA 1.3.1.16 の座標1面を表す操作。 -/
def pathCubeInsertFunctor {S : Finset (Set.Ioo a b)} (j : S) : Set ↥S ⥤ Set ↥S :=
  (show Monotone (fun U : Set ↥S ↦ insert j U) from
    fun _ _ h ↦ Set.insert_subset_insert h).functor

/-- 概要：内部点を挿入した Path は左右の区間に制限した Path の合成である。
方針：選んだ点を切断点との大小で分け、Path の合成の和集合と一致させる。
規約：関手の厳密な等式であり、通常の圏での合成を用いる。
使われ方：HA 1.3.1.16 の座標1面を二つの小さい区間の合成として表す。 -/
lemma pathCubeInsertFunctor_comp (hab : a < b) {S : Finset (Set.Ioo a b)} (j : S) :
    pathCubeInsertFunctor j ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeFunctor hab S =
      (pathCubeIntervalFunctor j.val.property.1 S).prod'
        (pathCubeIntervalFunctor j.val.property.2 S) ⋙
          compFunctor (.mk a) (.mk j.val.val) (.mk b) := by
  refine CategoryTheory.Functor.ext (fun U ↦ ?_)
  apply CategoryTheory.SimplicialThickening.Path.ext
  ext x
  change (x = a ∨ x = b ∨ ∃ hx : x ∈ Set.Ioo a b,
    (⟨x, hx⟩ : Set.Ioo a b) ∈ (Subtype.val : S → Set.Ioo a b) '' insert j U) ↔
    ((x = a ∨ x = j.val.val ∨ ∃ hx : x ∈ Set.Ioo a j.val.val,
      ∃ t : S, t ∈ U ∧ t.val.val = x) ∨
    (x = j.val.val ∨ x = b ∨ ∃ hx : x ∈ Set.Ioo j.val.val b,
      ∃ t : S, t ∈ U ∧ t.val.val = x))
  constructor
  · rintro (rfl | rfl | ⟨hx, t, ht, he⟩)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · have htx : t.val.val = x := congrArg Subtype.val he
      rcases ht with rfl | ht
      · exact Or.inl (Or.inr (Or.inl htx.symm))
      · rcases lt_trichotomy x j.val.val with h | h | h
        · exact Or.inl (Or.inr (Or.inr ⟨⟨hx.1, h⟩, t, ht, htx⟩))
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr ⟨⟨h, hx.2⟩, t, ht, htx⟩))
  · intro h
    rcases h with (rfl | h | ⟨hx, t, ht, he⟩) | (h | rfl | ⟨hx, t, ht, he⟩)
    · exact Or.inl rfl
    · subst x
      exact Or.inr (Or.inr ⟨j.val.property, j, Set.mem_insert j U, rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨hx.1, lt_trans hx.2 j.val.property.2⟩,
        t, Set.mem_insert_of_mem j ht, Subtype.ext he⟩)
    · subst x
      exact Or.inr (Or.inr ⟨j.val.property, j, Set.mem_insert j U, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨⟨lt_trans j.val.property.1 hx.1, hx.2⟩,
        t, Set.mem_insert_of_mem j ht, Subtype.ext he⟩)

/-- 概要：番号付きの座標1面は左右の区間の Path の合成を通る。
方針：残りの座標の0面に内部点を挿入し、関手の合成分解を各単体で使う。
規約：左右の Path は同じ残りの座標集合から作る。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面に豊穣関手の合成保存を適用する入口。 -/
lemma pathCubeMap_face_one (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S =
      nerveMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceOrder e i false).monotone.functor ⋙
        ((pathCubeIntervalFunctor (e i).val.property.1 S).prod'
          (pathCubeIntervalFunctor (e i).val.property.2 S) ⋙
            compFunctor (.mk a) (.mk (e i).val.val) (.mk b))) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  exact congrArg (fun G ↦ G.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceOrder e i false (F.obj t)))
    (pathCubeInsertFunctor_comp hab (e i))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
