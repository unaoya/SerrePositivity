module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FlagEquiv

/-!
概要：coherent な右 pinched 単体の旗による評価の次数に関する自然性。
方針：対象の移送を正規化し、path の添字変換と旗の直接像を比較する。
規約：任意の面と退化を単体圏の射として扱う。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、型の同値を単体集合の同型へまとめる準備。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：豊穣関手の Hom の作用は始域側の端点の等号の移送と整合する。
方針：始域の二つの等号を消去する。
規約：標的の二対象への正規化も含めて式を述べる。
使われ方：Kerodon §2.4.3（Tag 00KM）、pinched 単体の次数変換の端点の整理。 -/
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
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、評価の次数に関する自然性の Hom の部分。 -/
lemma coherentPinchedHom_pullback {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {m n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom (τ.pullback α) i =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor α i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom τ (α.toOrderHom i) := by
  let hi := congrArg (fun a : Fin (n + 2) ↦
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom i)
  let hj := congrArg (fun a : Fin (n + 2) ↦
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α.toOrderHom)
  have ht := enrichedFunctor_map_transport τ.val hi hj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_sourceObj τ (α.toOrderHom i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_targetObj τ)
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫
        eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
          (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom i)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α.toOrderHom))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom τ (α.toOrderHom i) := by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫
        τ.val.map ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom i.castSucc)⟩
          ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom (Fin.last (m + 1)))⟩) ≫
            eqToHom _ = _
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom, Category.assoc] using congrArg
        (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫ f) ht
    _ = _ := by
      rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫ _ =
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor α i) from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtend_map_cast_last α i]

/-- 概要：旗の path の添字変換は旗の直接像の path。
方針：元の集合の点と追加した終点に分け、直接像の所属を比較する。
規約：値域の単調写像は単射でなくてもよい。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、旗の解像の図式と path の添字変換の一致。 -/
lemma CoherentResolutionFlag.toPath_reindex {m n d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d) (α : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindex α (F.toPath.{u} k) = (F.pushforward α.toOrderHom).toPath k := by
  apply SimplicialThickening.Path.ext
  apply Set.ext
  intro l
  change (∃ p : ULift.{u} (Fin (m + 2)),
    (p.down = Fin.last (m + 1) ∨ ∃ j ∈ F.sets k, p.down = j.castSucc) ∧
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom p.down) = l) ↔
      l.down = Fin.last (n + 1) ∨
        ∃ j ∈ (F.sets k).image α.toOrderHom, l.down = j.castSucc
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with hp | ⟨j, hj, hp⟩
    · exact Or.inl ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom) hp).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α.toOrderHom))
    · exact Or.inr ⟨α.toOrderHom j, Finset.mem_image.mpr ⟨j, hj, rfl⟩,
        (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom) hp).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom j)⟩
  · rintro (hl | ⟨j, hj, hl⟩)
    · exact ⟨ULift.up (Fin.last (m + 1)), Or.inl rfl,
        ULift.ext ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α.toOrderHom).trans hl.symm)⟩
    · obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hj
      exact ⟨ULift.up p.castSucc, Or.inr ⟨p, hp, rfl⟩,
        ULift.ext ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom p).trans
          ((congrArg Fin.castSucc heq).trans hl.symm))⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentResolutionFlag (toPath_reindex)


/-- 概要：旗の path の単体の添字変換は直接像の旗の path の単体。
方針：各段の path の等号を関手の等号にする。
規約：旗の次数 d は固定し、値域の次数だけを変える。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、旗での評価の次数に関する自然性。 -/
lemma CoherentResolutionFlag.pathFlag_reindex {m n d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    F.pathFlag.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor α F.start =
      (F.pushforward α.toOrderHom).pathFlag := by
  apply CategoryTheory.Functor.ext (fun k ↦ F.toPath_reindex α k)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentResolutionFlag (pathFlag_reindex)


/-- 概要：pinched 単体の引き戻しの旗での評価は旗の直接像での評価。
方針：Hom の引き戻しを path の添字変換として表し、旗の直接像と照合する。
規約：面と退化を含む全ての次数変換に自然。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、写像の普遍性の次数に関する自然性。 -/
lemma coherentPinchedEvaluate_reindex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n d : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag m d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedEvaluate (τ.pullback α) F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedEvaluate τ (F.pushforward α.toOrderHom) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedEvaluate
  rw [coherentPinchedHom_pullback]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom τ (α.toOrderHom F.start)).app (Opposite.op ⦋d⦌)
    (F.pathFlag ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor α F.start) = _
  rw [F.pathFlag_reindex]
  rfl

/-- 概要：旗の評価射は pinched 単体の次数変換を解像の射による前合成へ移す。
方針：各次数の各旗で評価の自然性を使う。
規約：単体集合の射の等式として述べる。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、制限 Yoneda 関手との自然同型。 -/
lemma coherentPinchedFlagMap_reindex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap (τ.pullback α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap α.toOrderHom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap τ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  exact coherentPinchedEvaluate_reindex τ α F.down

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
