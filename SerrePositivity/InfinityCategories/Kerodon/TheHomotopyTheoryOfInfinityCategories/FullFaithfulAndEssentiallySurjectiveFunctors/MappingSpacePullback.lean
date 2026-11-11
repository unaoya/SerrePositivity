module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PullbackSimplex

/-!
概要：引き戻しの右 pinched 写像空間への単体の持ち上げ。
方針：各次数で一致する二つの単体を引き戻しに持ち上げ、固定端点を両射影で確認する。
規約：Mathlib の引き戻しと N レーンの pinched 模型をそのまま使う。
使われ方：Kerodon Proposition 4.8.4.5（Tag 05AR） の標準単体への基底変換。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：一致する二つの pinched 単体を引き戻しの pinched 単体へ持ち上げる。
方針：元の単体を引き戻しに入れ、両射影で定値面と最後の頂点を確認する。
規約：端点は引き戻しの指定された二頂点。
使われ方：Kerodon §4.8.4（Tag 06SQ） の写像空間の基底変換。 -/
noncomputable def pinchedPullbackSimplex {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) {n : ℕ}
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.fst p q).app (Opposite.op ⦋0⦌) w)) _⦋n⦌)
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w)) _⦋n⦌)
    (h : p.app (Opposite.op ⦋n + 1⦌) x.val = q.app (Opposite.op ⦋n + 1⦌) y.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom v w) _⦋n⦌ := by
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex p q x.val y.val h
  refine ⟨z, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_ext p q
    · calc
        _ = X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op
            ((pullback.fst p q).app (Opposite.op ⦋n + 1⦌) z) :=
          ConcreteCategory.congr_hom ((pullback.fst p q).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op) z
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((pullback.fst p q).app (Opposite.op ⦋0⦌) v) n := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_fst]
          exact x.source
        _ = (pullback.fst p q).app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n) :=
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map _ _ _).symm
    · calc
        _ = Y.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op
            ((pullback.snd p q).app (Opposite.op ⦋n + 1⦌) z) :=
          ConcreteCategory.congr_hom ((pullback.snd p q).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op) z
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((pullback.snd p q).app (Opposite.op ⦋0⦌) v) n := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_snd]
          exact y.source
        _ = (pullback.snd p q).app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n) :=
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map _ _ _).symm
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_ext p q
    · calc
        _ = X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op
            ((pullback.fst p q).app (Opposite.op ⦋n + 1⦌) z) :=
          ConcreteCategory.congr_hom ((pullback.fst p q).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op) z
        _ = (pullback.fst p q).app (Opposite.op ⦋0⦌) w := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_fst]
          exact x.target
    · calc
        _ = Y.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op
            ((pullback.snd p q).app (Opposite.op ⦋n + 1⦌) z) :=
          ConcreteCategory.congr_hom ((pullback.snd p q).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op) z
        _ = (pullback.snd p q).app (Opposite.op ⦋0⦌) w := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_snd]
          exact y.target

/-- 概要：pinched 単体の持ち上げの第一射影は元の単体。
方針：引き戻しの第一射影の式を適用する。
規約：端点の表示も射影で与える。
使われ方：Kerodon §4.8.4（Tag 06SQ） の基底変換の成分。 -/
lemma pinchedPullbackSimplex_fst {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) {n : ℕ} (x y) (h) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.fst p q) v w).app (Opposite.op ⦋n⦌)
      (pinchedPullbackSimplex p q v w x y h) = x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_fst p q x.val y.val h

/-- 概要：pinched 単体の持ち上げの第二射影は元の単体。
方針：引き戻しの第二射影の式を適用する。
規約：端点の表示も射影で与える。
使われ方：Kerodon §4.8.4（Tag 06SQ） の基底変換の成分。 -/
lemma pinchedPullbackSimplex_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) {n : ℕ} (x y) (h) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w).app (Opposite.op ⦋n⦌)
      (pinchedPullbackSimplex p q v w x y h) = y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_snd p q x.val y.val h

/-- 概要：一致する二つの写像空間の族を引き戻しの写像空間へ持ち上げる。
方針：各単体を引き戻しに持ち上げ、両射影の自然性を使う。
規約：一致条件は元の標的の単体の値に課す。
使われ方：Kerodon §4.8.4（Tag 06SQ） の写像空間の基底変換。 -/
noncomputable def pinchedHomPullbackLift {A X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.fst p q).app (Opposite.op ⦋0⦌) w))
    (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w))
    (hc : ∀ (n : ℕ) (a : A _⦋n⦌),
      p.app (Opposite.op ⦋n + 1⦌) (f.app (Opposite.op ⦋n⦌) a).val =
        q.app (Opposite.op ⦋n + 1⦌) (g.app (Opposite.op ⦋n⦌) a).val) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom v w where
  app n := by
    obtain ⟨⟨d⟩⟩ := n
    exact ↾(fun a ↦ pinchedPullbackSimplex p q v w (f.app _ a) (g.app _ a) (hc d a))
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro a
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex p q (f.app _ (A.map α a)).val (g.app _ (A.map α a)).val (hc m (A.map α a)) =
      (pullback p q).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex p q (f.app _ a).val (g.app _ a).val (hc n a))
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_ext p q
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_fst]
      symm
      calc
        _ = X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op
            ((pullback.fst p q).app (Opposite.op ⦋n + 1⦌)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex p q (f.app _ a).val (g.app _ a).val (hc n a))) :=
          ConcreteCategory.congr_hom ((pullback.fst p q).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op) _
        _ = X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op (f.app _ a).val := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_fst]
        _ = (f.app _ (A.map α a)).val := by
          have h := ConcreteCategory.congr_hom (f.naturality α) a
          change f.app (Opposite.op ⦋m⦌) (A.map α a) =
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom _ _).map α (f.app (Opposite.op ⦋n⦌) a) at h
          exact congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
            ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
            ((pullback.fst p q).app (Opposite.op ⦋0⦌) w)) _⦋m⦌ ↦ z.val) h.symm
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_snd]
      symm
      calc
        _ = Y.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op
            ((pullback.snd p q).app (Opposite.op ⦋n + 1⦌)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex p q (f.app _ a).val (g.app _ a).val (hc n a))) :=
          ConcreteCategory.congr_hom ((pullback.snd p q).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op) _
        _ = Y.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op (g.app _ a).val := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_snd]
        _ = (g.app _ (A.map α a)).val := by
          have h := ConcreteCategory.congr_hom (g.naturality α) a
          change g.app (Opposite.op ⦋m⦌) (A.map α a) =
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom _ _).map α (g.app (Opposite.op ⦋n⦌) a) at h
          exact congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
            ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
            ((pullback.snd p q).app (Opposite.op ⦋0⦌) w)) _⦋m⦌ ↦ z.val) h.symm

/-- 概要：写像空間の族の持ち上げの第一射影は元の族。
方針：各単体の第一射影を比較する。
規約：任意のパラメーター単体集合。
使われ方：Kerodon §4.8.4（Tag 06SQ） の基底変換の射の比較。 -/
lemma pinchedHomPullbackLift_fst {A X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) (f g hc) :
    pinchedHomPullbackLift (A := A) p q v w f g hc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.fst p q) v w = f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  exact pinchedPullbackSimplex_fst p q v w (f.app _ a) (g.app _ a) (hc n a)

/-- 概要：写像空間の族の持ち上げの第二射影は元の族。
方針：各単体の第二射影を比較する。
規約：任意のパラメーター単体集合。
使われ方：Kerodon §4.8.4（Tag 06SQ） の基底変換の射の比較。 -/
lemma pinchedHomPullbackLift_snd {A X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) (f g hc) :
    pinchedHomPullbackLift (A := A) p q v w f g hc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  exact pinchedPullbackSimplex_snd p q v w (f.app _ a) (g.app _ a) (hc n a)

/-- 概要：引き戻しの写像空間への射は両方の射影で決まる。
方針：各 pinched 単体の元の単体を両射影で比較する。
規約：任意のパラメーター単体集合。
使われ方：Kerodon §4.8.4（Tag 06SQ） の基底変換の持ち上げの一意性。 -/
lemma pinchedHomPullback_hom_ext {A X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom v w}
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.fst p q) v w = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.fst p q) v w)
    (hs : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w) :
    f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_ext p q
  · exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val
      (ConcreteCategory.congr_hom (NatTrans.congr_app hf (Opposite.op ⦋n⦌)) a)
  · exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val
      (ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋n⦌)) a)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
