module
public import SerrePositivity.KST.SConstruction.CofiberRows
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pasting

/-! # 三つ組の cofiber 条件から gapped 条件へ
概要：BGT Definition 7.1 の三つ組の正方形の普遍性から全四つ組の押し出し性を導く。
方針：三つ組の正方形を左側・外側とする長方形に押し出しの相殺を適用する。
規約：零対角条件は独立に保持する。使われ方：BGT Lemma 7.3、HTT Lemma 4.4.2.1。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：三つの順序づけられた端点から二単体の順序写像を作る。
方針：有限集合の三つの場合を直接指定する。
規約：端点の一致を許す。使われ方：二四角形を貼り合わせた長方形の横方向。 -/
def intervalTriple {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c) :
    Fin 3 →o Fin (n + 1) where
  toFun x := if x = 0 then a else if x = 1 then b else c
  monotone' x y h := by
    fin_cases x <;> fin_cases y <;> simp_all
    exact hab.trans hbc

/-- 概要：三つ組の正方形を二つ含む Ar[n] の長方形の順序写像。
方針：横は j→k→l、縦は i→j を取る。
規約：i≤j≤k≤l。使われ方：三つ組の条件から全四つ組への還元。 -/
def arCofiberRectangleOrder {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    ULift.{u} (Fin 3 × Fin 2) →o Ar.{u} n where
  toFun x := arObj (intervalStep i j hij x.down.2)
    (intervalTriple j k l hjk hkl x.down.1) (by
      apply (intervalStep_le i j hij _).trans
      have h : (0 : Fin 3) ≤ x.down.1 := Fin.zero_le _
      exact (intervalTriple j k l hjk hkl).monotone h)
  monotone' _ _ h := ⟨(intervalStep i j hij).monotone h.2,
    (intervalTriple j k l hjk hkl).monotone h.1⟩

/-- 概要：Ar[n] 内の cofiber 長方形を単体集合の射にする。
方針：標準単体の積の nerve 表示と順序関手を合成する。
規約：二単体が横、標準辺が縦。使われ方：押し出しの貼り合わせ定理の適用。 -/
def arCofiberRectangle {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n :=
  (prodStdSimplex.isoNerve 2 1).hom ≫
    nerveMap (arCofiberRectangleOrder i j k l hij hjk hkl).toFunctor

/-- 概要：長方形の左の面は (i,j,j,k) の三つ組の正方形。
方針：横の最初の二端点を選ぶ。
規約：面番号2。使われ方：左押し出しの入力。 -/
lemma arCofiberRectangle_left {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 2 =
      arSquare i j j k hij le_rfl hjk := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change intervalTriple j k l hjk hkl
      ((SimplexCategory.δ (2 : Fin 3)).toOrderHom (stdSimplex.asOrderHom s.1 r)) =
        intervalStep j k hjk (stdSimplex.asOrderHom s.1 r)
    generalize hx : stdSimplex.asOrderHom s.1 r = x
    fin_cases x <;> rfl

/-- 概要：長方形の外側は (i,j,j,l) の三つ組の正方形。
方針：横の最初と最後の端点を選ぶ。
規約：面番号1。使われ方：外側押し出しの入力。 -/
lemma arCofiberRectangle_outer {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 1 =
      arSquare i j j l hij le_rfl (hjk.trans hkl) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change intervalTriple j k l hjk hkl
      ((SimplexCategory.δ (1 : Fin 3)).toOrderHom (stdSimplex.asOrderHom s.1 r)) =
        intervalStep j l (hjk.trans hkl) (stdSimplex.asOrderHom s.1 r)
    generalize hx : stdSimplex.asOrderHom s.1 r = x
    fin_cases x <;> rfl

/-- 概要：長方形の右側は一般の (i,j,k,l) の正方形。
方針：横の最後の二端点を選ぶ。
規約：面番号0。使われ方：押し出しの相殺の結論。 -/
lemma arCofiberRectangle_right {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 0 =
      arSquare i j k l hij hjk hkl := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change intervalTriple j k l hjk hkl
      ((SimplexCategory.δ (0 : Fin 3)).toOrderHom (stdSimplex.asOrderHom s.1 r)) =
        intervalStep k l hkl (stdSimplex.asOrderHom s.1 r)
    generalize hx : stdSimplex.asOrderHom s.1 r = x
    fin_cases x <;> rfl

/-- 概要：三つ組の cofiber 正方形が全て押し出しなら全四つ組の正方形が押し出し。
方針：二つの三つ組を左側と外側に置き、押し出しの相殺を使う。
規約：C は quasicategory。零対角や安定性はこの含意には不要。
使われ方：BGT Definition 7.1 と全四角形条件の同値。 -/
lemma arSquares_isPushout_of_triples {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : arNerve n ⟶ C)
    (hF : ∀ (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare i j j k hij le_rfl hjk ≫ F))
    (i j k l : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare i j k l hij hjk hkl ≫ F) := by
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle i j k l hij hjk hkl ≫ F) 2) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 2 ≫ F)
    rw [arCofiberRectangle_left]
    exact hF i j k hij hjk
  have houter : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle i j k l hij hjk hkl ≫ F) 1) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 1 ≫ F)
    rw [arCofiberRectangle_outer]
    exact hF i j l hij (hjk.trans hkl)
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting_cancel_left _ hleft houter
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 0 ≫ F) at h
  rwa [arCofiberRectangle_right] at h

/-- 概要：零対角を持つ図式の gapped 条件は全三つ組の cofiber 正方形の普遍性と同値。
方針：一方向は四つ組の中間二端点を等しくし、逆方向は貼り合わせで示す。
規約：C は quasicategory。使われ方：第一行からの構成で確認すべき条件の削減。 -/
lemma isGapped_iff_triples {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : arNerve n ⟶ C) : IsGapped F ↔
      (∀ i : Fin (n + 1), _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (arObj i i le_rfl)))) ∧
      (∀ (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare i j j k hij le_rfl hjk ≫ F)) := by
  constructor
  · intro h
    exact ⟨h.1, fun i j k hij hjk => h.2 i j j k hij le_rfl hjk⟩
  · rintro ⟨hz, ht⟩
    exact ⟨hz, arSquares_isPushout_of_triples F ht⟩

end SerrePositivity.KST.SConstruction
