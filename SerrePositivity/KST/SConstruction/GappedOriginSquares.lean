module
public import SerrePositivity.KST.SConstruction.GappedTriples
public import SerrePositivity.KST.SConstruction.ArCofiberFamily
public import SerrePositivity.KST.SConstruction.PushoutTranspose

/-! # 第一行からの cofiber 正方形による gapped 性の判定
概要：全区間の標準 cofiber 正方形の普遍性だけで全四つ組の押し出し性を判定する。
方針：横方向と縦方向で二回、押し出しの相殺を使う。
規約：零対角条件は別に課す。使われ方：BGT Lemma 7.3 の第一行からの復元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：転置した三正方形を貼る長方形の順序写像。
方針：第一端点を i→j→k、第二端点を k→l とする。
規約：長方形の横が元の縦方向。使われ方：縦方向の押し出しの相殺。 -/
def arVerticalRectangleOrder {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    ULift.{u} (Fin 3 × Fin 2) →o Ar.{u} n where
  toFun x := arObj (intervalTriple i j k hij hjk x.down.1)
    (intervalStep k l hkl x.down.2) (by
      apply le_trans ((intervalTriple i j k hij hjk).monotone (Fin.le_last _))
      exact le_intervalStep k l hkl _)
  monotone' _ _ h := ⟨(intervalTriple i j k hij hjk).monotone h.1,
    (intervalStep k l hkl).monotone h.2⟩

/-- 概要：縦に貼った三正方形を転置した長方形の単体集合の射。
方針：標準単体の積の nerve 表示と順序関手を合成する。
規約：二単体が第一因子。使われ方：通常の横方向の貼り合わせ定理への接続。 -/
def arVerticalRectangle {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n :=
  (prodStdSimplex.isoNerve 2 1).hom ≫
    nerveMap (arVerticalRectangleOrder i j k l hij hjk hkl).toFunctor

/-- 概要：縦長方形の左面は上側正方形の転置。
方針：二単体の最初の二端点を選ぶ。
規約：面番号2。使われ方：押し出しの相殺の左面。 -/
lemma arVerticalRectangle_left {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arVerticalRectangle i j k l hij hjk hkl) 2 =
      (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ arSquare i j k l hij hjk hkl := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change intervalTriple i j k hij hjk
      ((SimplexCategory.δ (2 : Fin 3)).toOrderHom (stdSimplex.asOrderHom s.1 r)) =
        intervalStep i j hij (stdSimplex.asOrderHom s.1 r)
    generalize hx : stdSimplex.asOrderHom s.1 r = x
    fin_cases x <;> rfl
  · rfl

/-- 概要：縦長方形の外側は外側正方形の転置。
方針：二単体の最初と最後の端点を選ぶ。
規約：面番号1。使われ方：押し出しの相殺の外側。 -/
lemma arVerticalRectangle_outer {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arVerticalRectangle i j k l hij hjk hkl) 1 =
      (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫
        arSquare i k k l (hij.trans hjk) le_rfl hkl := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change intervalTriple i j k hij hjk
      ((SimplexCategory.δ (1 : Fin 3)).toOrderHom (stdSimplex.asOrderHom s.1 r)) =
        intervalStep i k (hij.trans hjk) (stdSimplex.asOrderHom s.1 r)
    generalize hx : stdSimplex.asOrderHom s.1 r = x
    fin_cases x <;> rfl
  · rfl

/-- 概要：縦長方形の右面は下側正方形の転置。
方針：二単体の最後の二端点を選ぶ。
規約：面番号0。使われ方：押し出しの相殺の結論。 -/
lemma arVerticalRectangle_right {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arVerticalRectangle i j k l hij hjk hkl) 0 =
      (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ arSquare j k k l hjk le_rfl hkl := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change intervalTriple i j k hij hjk
      ((SimplexCategory.δ (0 : Fin 3)).toOrderHom (stdSimplex.asOrderHom s.1 r)) =
        intervalStep j k hjk (stdSimplex.asOrderHom s.1 r)
    generalize hx : stdSimplex.asOrderHom s.1 r = x
    fin_cases x <;> rfl
  · rfl

/-- 概要：第一行を上辺に持つ標準 cofiber 正方形の普遍性から三つ組の普遍性が従う。
方針：横方向の相殺で (0,i,j,k) を得て、縦方向の相殺で (i,j,j,k) を得る。
規約：C は quasicategory、安定性や零対角条件は不要。
使われ方：補完後の図式自身の gapped 性の判定。 -/
lemma arTriple_isPushout_of_originSquares {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : arNerve n ⟶ C)
    (hF : ∀ (i j : Fin (n + 1)) (hij : i ≤ j),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare 0 i i j (Fin.zero_le _) le_rfl hij ≫ F))
    (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare i j j k hij le_rfl hjk ≫ F) := by
  have htop : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare 0 i j k (Fin.zero_le _) hij hjk ≫ F) := by
    have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle 0 i j k (Fin.zero_le _) hij hjk ≫ F) 2) := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle 0 i j k (Fin.zero_le _) hij hjk) 2 ≫ F)
      rw [arCofiberRectangle_left]
      exact hF i j hij
    have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle 0 i j k (Fin.zero_le _) hij hjk ≫ F) 1) := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle 0 i j k (Fin.zero_le _) hij hjk) 1 ≫ F)
      rw [arCofiberRectangle_outer]
      exact hF i k (hij.trans hjk)
    have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting_cancel_left _ hl ho
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arCofiberRectangle 0 i j k (Fin.zero_le _) hij hjk) 0 ≫ F) at ht
    rwa [arCofiberRectangle_right] at ht
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arVerticalRectangle 0 i j k (Fin.zero_le _) hij hjk ≫ F) 2) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arVerticalRectangle 0 i j k (Fin.zero_le _) hij hjk) 2 ≫ F)
    rw [arVerticalRectangle_left, Category.assoc]
    exact IsPushoutSquare.transpose htop
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arVerticalRectangle 0 i j k (Fin.zero_le _) hij hjk ≫ F) 1) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arVerticalRectangle 0 i j k (Fin.zero_le _) hij hjk) 1 ≫ F)
    rw [arVerticalRectangle_outer, Category.assoc]
    exact IsPushoutSquare.transpose (hF j k hjk)
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting_cancel_left _ hl ho
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (arVerticalRectangle 0 i j k (Fin.zero_le _) hij hjk) 0 ≫ F) at ht
  rw [arVerticalRectangle_right, Category.assoc] at ht
  have ht' := IsPushoutSquare.transpose ht
  simpa only [← Category.assoc, Iso.hom_inv_id, SymmetricCategory.symmetry,
    Category.id_comp] using ht'

/-- 概要：零対角を持つ図式の gapped 性は標準 cofiber 正方形の普遍性と同値。
方針：標準正方形から全三つ組、全四つ組へ押し出しの相殺で進む。
規約：C は quasicategory。使われ方：第一行からの復元で残る普遍性の正確な形。 -/
lemma isGapped_iff_originSquares {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : arNerve n ⟶ C) : IsGapped F ↔
      (∀ i : Fin (n + 1), _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (arObj i i le_rfl)))) ∧
      (∀ (i j : Fin (n + 1)) (hij : i ≤ j),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare 0 i i j (Fin.zero_le _) le_rfl hij ≫ F)) := by
  constructor
  · intro h
    exact ⟨h.1, fun i j hij => h.2 0 i i j (Fin.zero_le _) le_rfl hij⟩
  · rintro ⟨hz, ho⟩
    exact (isGapped_iff_triples F).2 ⟨hz, arTriple_isPushout_of_originSquares F ho⟩

/-- 概要：図式の gapped 性は、その標準 cofiber 抽出の全頂点の cofiber 条件と同値。
方針：各区間の cofiber 正方形の頂点評価と第一行からの判定を合わせる。
規約：C は quasicategory。使われ方：補完された実際の図式と cofiber 族の接続。 -/
lemma isGapped_iff_arCofiberFamily_vertices {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : arNerve n ⟶ C) : IsGapped F ↔
      ∀ a : (arNerve n) _⦋0⦌,
        IsCofiberDiagramVertex ((arCofiberFamily F).app (Opposite.op ⦋0⦌) a) := by
  constructor
  · intro h a
    have ha : a = ComposableArrows.mk₀ (nerveEquiv a) :=
      (nerveEquiv.symm_apply_apply a).symm
    rw [ha, arCofiberFamily_vertex]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex
      (arSquare 0 (nerveEquiv a).down.val.1 (nerveEquiv a).down.val.1
        (nerveEquiv a).down.val.2 (Fin.zero_le _) le_rfl (nerveEquiv a).down.property ≫ F) 0 1) ∧ _
    exact ⟨h.1 (nerveEquiv a).down.val.1,
      h.2 0 _ _ _ (Fin.zero_le _) le_rfl (nerveEquiv a).down.property⟩
  · intro h
    apply (isGapped_iff_originSquares F).2
    constructor
    · intro i
      have hi := h (ComposableArrows.mk₀ (arObj i i le_rfl))
      rw [arCofiberFamily_vertex] at hi
      exact hi.1
    · intro i j hij
      have hij' := h (ComposableArrows.mk₀ (arObj i j hij))
      rw [arCofiberFamily_vertex] at hij'
      exact hij'.2

end SerrePositivity.KST.SConstruction
