module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PullbackRightComposition

/-!
概要：二つの引き戻しを組み替える zigzag 図式の普遍性。
方針：三つの座標の整合条件を二通りの順序で引き戻す。
規約：通常の単体集合の引き戻しのみを使う。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆 path による共通の解像。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：二つの基底を結ぶ中間対象を持つ zigzag の引き戻し。
方針：先に右側を引き戻してから左側を引き戻す。
規約：f:A→S、g:B→S、h:B→T、k:C→T。
使われ方：Kerodon §4.5.3（Tag 032Y） の path を挟む引き戻し。 -/
noncomputable def pullbackZigzag {A B C S T : SSet.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (h : B ⟶ T) (k : C ⟶ T) : SSet.{u} :=
  pullback f (pullback.fst h k ≫ g)

/-- 概要：zigzag の引き戻しから左の引き戻しへの射。
方針：中間座標と左座標を組にする。
規約：左の引き戻しは B と A の順。
使われ方：Kerodon §4.5.3（Tag 032Y） の引き戻しの組み替え。 -/
noncomputable def pullbackZigzagLeft {A B C S T : SSet.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (h : B ⟶ T) (k : C ⟶ T) :
    pullbackZigzag f g h k ⟶ pullback g f :=
  pullback.lift (pullback.snd f (pullback.fst h k ≫ g) ≫ pullback.fst h k)
    (pullback.fst f (pullback.fst h k ≫ g)) (by
      rw [Category.assoc, ← pullback.condition])

/-- 概要：zigzag の引き戻しから右の対象への射影。
方針：二つの第二射影を合成する。
規約：最後の対象 C を返す。
使われ方：Kerodon §4.5.3（Tag 032Y） の共通の解像の射影。 -/
noncomputable def pullbackZigzagRight {A B C S T : SSet.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (h : B ⟶ T) (k : C ⟶ T) :
    pullbackZigzag f g h k ⟶ C :=
  pullback.snd f (pullback.fst h k ≫ g) ≫ pullback.snd h k

/-- 概要：zigzag の左比較の第一成分は中間座標。
方針：lift の第一射影を計算する。
規約：左の引き戻しの順序は B、A。
使われ方：Kerodon §4.5.3（Tag 032Y） の普遍性の検証。 -/
lemma pullbackZigzagLeft_fst {A B C S T : SSet.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (h : B ⟶ T) (k : C ⟶ T) :
    pullbackZigzagLeft f g h k ≫ pullback.fst g f =
      pullback.snd f (pullback.fst h k ≫ g) ≫ pullback.fst h k :=
  pullback.lift_fst _ _ _

/-- 概要：zigzag の左比較の第二成分は左座標。
方針：lift の第二射影を計算する。
規約：左の引き戻しの順序は B、A。
使われ方：Kerodon §4.5.3（Tag 032Y） の普遍性の検証。 -/
lemma pullbackZigzagLeft_snd {A B C S T : SSet.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (h : B ⟶ T) (k : C ⟶ T) :
    pullbackZigzagLeft f g h k ≫ pullback.snd g f =
      pullback.fst f (pullback.fst h k ≫ g) := pullback.lift_snd _ _ _

/-- 概要：zigzag の比較と右射影は左の引き戻しからの射の引き戻しを与える。
方針：中間・左・右の三つの座標の外延性と入れ子の lift を使う。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の持ち上げ性の移送。 -/
lemma pullbackZigzag_isPullback {A B C S T : SSet.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (h : B ⟶ T) (k : C ⟶ T) :
    IsPullback (pullbackZigzagLeft f g h k) (pullbackZigzagRight f g h k)
      (pullback.fst g f ≫ h) k := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← Category.assoc, pullbackZigzagLeft_fst, Category.assoc, pullback.condition,
      ← Category.assoc]
    rfl
  · intro Z φ ψ h₀ h₁
    apply pullback.hom_ext
    · have he := congrArg (fun z ↦ z ≫ pullback.snd g f) h₀
      simpa only [Category.assoc, pullbackZigzagLeft_snd] using he
    · apply pullback.hom_ext
      · have he := congrArg (fun z ↦ z ≫ pullback.fst g f) h₀
        simpa only [Category.assoc, pullbackZigzagLeft_fst] using he
      · simpa only [pullbackZigzagRight, Category.assoc] using h₁
  · intro Z a b hab
    let R := pullback.lift (a ≫ pullback.fst g f) b (by
      simpa only [Category.assoc] using hab)
    have hw : (a ≫ pullback.snd g f) ≫ f = R ≫ (pullback.fst h k ≫ g) := by
      rw [Category.assoc, ← pullback.condition]
      have he := congrArg (fun z ↦ z ≫ g)
        (show R ≫ pullback.fst h k = a ≫ pullback.fst g f from pullback.lift_fst _ _ _)
      simpa only [Category.assoc] using he.symm
    let F := pullback.lift (a ≫ pullback.snd g f) R hw
    refine ⟨F, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, pullbackZigzagLeft_fst, ← Category.assoc,
          pullback.lift_snd, pullback.lift_fst]
      · rw [Category.assoc, pullbackZigzagLeft_snd, pullback.lift_fst]
    · change F ≫ (pullback.snd _ _ ≫ pullback.snd h k) = b
      rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- 概要：左の引き戻しから基底への射が trivial Kan fibration なら zigzag の右射影もそうなる。
方針：前の普遍性により基底変換として移す。
規約：元の対象の quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の同値の引き戻しの比較。 -/
lemma trivialKanFibration_pullbackZigzagRight {A B C S T : SSet.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (h : B ⟶ T) (k : C ⟶ T)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.fst g f ≫ h)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullbackZigzagRight f g h k) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback (pullbackZigzag_isPullback f g h k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := pullback.fst g f ≫ h))⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
