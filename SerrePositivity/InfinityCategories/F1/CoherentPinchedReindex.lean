module

public import SerrePositivity.InfinityCategories.F1.CoherentFlagEquiv

/-!
概要：coherent な右 pinched 単体の旗による評価の次数に関する自然性。
方針：対象の移送を正規化し、path の添字変換と旗の直接像を比較する。
規約：任意の面と退化を単体圏の射として扱う。
使われ方：Kerodon Proposition 4.6.7.16、型の同値を単体集合の同型へまとめる準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：豊穣関手の Hom の作用は始域側の端点の等号の移送と整合する。
方針：始域の二つの等号を消去する。
規約：標的の二対象への正規化も含めて式を述べる。
使われ方：Kerodon §2.4.3、pinched 単体の次数変換の端点の整理。 -/
lemma enrichedFunctor_map_transport {A : Type w} {C : Type v}
    [EnrichedCategory SSet.{u} A] [Category.{u} C] [SimplicialCategory C]
    (T : EnrichedFunctor SSet.{u} A C) {i j i' j' : A} (hi : i = i') (hj : j = j')
    {X Y : C} (hX : T.obj i' = X) (hY : T.obj j' = Y) :
    T.map i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg T.obj hi).trans hX) ((congrArg T.obj hj).trans hY)) =
      eqToHom (congrArg₂ (fun a b : A ↦ (a ⟶[SSet.{u}] b)) hi hj) ≫
        T.map i' j' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hX hY) := by
  subst i'
  subst j'
  simp

/-- 概要：pinched 単体の引き戻しの正規化した Hom は path の添字変換による前合成。
方針：豊穣関手の合成を展開し、二端点を移して既存の path の添字変換と照合する。
規約：追加した最後の頂点を固定する延長を使う。
使われ方：Kerodon Proposition 4.6.7.16、評価の次数に関する自然性の Hom の部分。 -/
lemma coherentPinchedHom_pullback {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {m n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    coherentPinchedHom (τ.pullback α) i =
      nerveMap (pathLastReindexFunctor α i) ≫ coherentPinchedHom τ (α.toOrderHom i) := by
  let hi := congrArg (fun a : Fin (n + 2) ↦
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (PinchedHom.extendOrderHom_castSucc α.toOrderHom i)
  let hj := congrArg (fun a : Fin (n + 2) ↦
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (PinchedHom.extendOrderHom_last α.toOrderHom)
  have ht := enrichedFunctor_map_transport τ.val hi hj
    (coherentPinched_sourceObj τ (α.toOrderHom i)) (coherentPinched_targetObj τ)
  calc
    _ = (thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫
        eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
          (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
          (PinchedHom.extendOrderHom_castSucc α.toOrderHom i)
          (PinchedHom.extendOrderHom_last α.toOrderHom))) ≫
          coherentPinchedHom τ (α.toOrderHom i) := by
      change (thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫
        τ.val.map ⟨ULift.up (PinchedHom.extendOrderHom α.toOrderHom i.castSucc)⟩
          ⟨ULift.up (PinchedHom.extendOrderHom α.toOrderHom (Fin.last (m + 1)))⟩) ≫
            eqToHom _ = _
      simpa only [coherentPinchedHom, Category.assoc] using congrArg
        (fun f ↦ thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫ f) ht
    _ = _ := by
      rw [show thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫ _ =
        nerveMap (pathLastReindexFunctor α i) from thickeningExtend_map_cast_last α i]

/-- 概要：旗の path の添字変換は旗の直接像の path。
方針：元の集合の点と追加した終点に分け、直接像の所属を比較する。
規約：値域の単調写像は単射でなくてもよい。
使われ方：Kerodon Example 4.6.7.27、旗の解像の図式と path の添字変換の一致。 -/
lemma CoherentResolutionFlag.toPath_reindex {m n d : ℕ}
    (F : CoherentResolutionFlag m d) (α : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (d + 1)) :
    pathLastReindex α (F.toPath.{u} k) = (F.pushforward α.toOrderHom).toPath k := by
  apply SimplicialThickening.Path.ext
  apply Set.ext
  intro l
  change (∃ p : ULift.{u} (Fin (m + 2)),
    (p.down = Fin.last (m + 1) ∨ ∃ j ∈ F.sets k, p.down = j.castSucc) ∧
      ULift.up (PinchedHom.extendOrderHom α.toOrderHom p.down) = l) ↔
      l.down = Fin.last (n + 1) ∨
        ∃ j ∈ (F.sets k).image α.toOrderHom, l.down = j.castSucc
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with hp | ⟨j, hj, hp⟩
    · exact Or.inl ((congrArg (PinchedHom.extendOrderHom α.toOrderHom) hp).trans
        (PinchedHom.extendOrderHom_last α.toOrderHom))
    · exact Or.inr ⟨α.toOrderHom j, Finset.mem_image.mpr ⟨j, hj, rfl⟩,
        (congrArg (PinchedHom.extendOrderHom α.toOrderHom) hp).trans
          (PinchedHom.extendOrderHom_castSucc α.toOrderHom j)⟩
  · rintro (hl | ⟨j, hj, hl⟩)
    · exact ⟨ULift.up (Fin.last (m + 1)), Or.inl rfl,
        ULift.ext ((PinchedHom.extendOrderHom_last α.toOrderHom).trans hl.symm)⟩
    · obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hj
      exact ⟨ULift.up p.castSucc, Or.inr ⟨p, hp, rfl⟩,
        ULift.ext ((PinchedHom.extendOrderHom_castSucc α.toOrderHom p).trans
          ((congrArg Fin.castSucc heq).trans hl.symm))⟩

/-- 概要：旗の path の単体の添字変換は直接像の旗の path の単体。
方針：各段の path の等号を関手の等号にする。
規約：旗の次数 d は固定し、値域の次数だけを変える。
使われ方：Kerodon Proposition 4.6.7.16、旗での評価の次数に関する自然性。 -/
lemma CoherentResolutionFlag.pathFlag_reindex {m n d : ℕ}
    (F : CoherentResolutionFlag m d) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    F.pathFlag.{u} ⋙ pathLastReindexFunctor α F.start =
      (F.pushforward α.toOrderHom).pathFlag := by
  apply CategoryTheory.Functor.ext (fun k ↦ F.toPath_reindex α k)

/-- 概要：pinched 単体の引き戻しの旗での評価は旗の直接像での評価。
方針：Hom の引き戻しを path の添字変換として表し、旗の直接像と照合する。
規約：面と退化を含む全ての次数変換に自然。
使われ方：Kerodon Proposition 4.6.7.16、写像の普遍性の次数に関する自然性。 -/
lemma coherentPinchedEvaluate_reindex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n d : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (F : CoherentResolutionFlag m d) :
    coherentPinchedEvaluate (τ.pullback α) F =
      coherentPinchedEvaluate τ (F.pushforward α.toOrderHom) := by
  unfold coherentPinchedEvaluate
  rw [coherentPinchedHom_pullback]
  change (coherentPinchedHom τ (α.toOrderHom F.start)).app (Opposite.op ⦋d⦌)
    (F.pathFlag ⋙ pathLastReindexFunctor α F.start) = _
  rw [F.pathFlag_reindex]
  rfl

/-- 概要：旗の評価射は pinched 単体の次数変換を解像の射による前合成へ移す。
方針：各次数の各旗で評価の自然性を使う。
規約：単体集合の射の等式として述べる。
使われ方：Kerodon Proposition 4.6.7.16、制限 Yoneda 関手との自然同型。 -/
lemma coherentPinchedFlagMap_reindex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    coherentPinchedFlagMap (τ.pullback α) =
      coherentResolutionMap α.toOrderHom ≫ coherentPinchedFlagMap τ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  exact coherentPinchedEvaluate_reindex τ α F.down

end SerrePositivity.InfinityCategories
