module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-! # Ar[n] と gapped 図式
概要：順序区間の圏とその nerve を定義する。
方針：成分ごとの順序とその関手性を使う。
規約：BGT Definition 7.1。使われ方：∞-S• 構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：Ar[n] の対象は i≤j を満たす対。
方針：成分ごとの順序を部分型と宇宙持ち上げで継承する。
規約：BGT Definition 7.1。使われ方：gapped 図式の添字圏。 -/
abbrev Ar (n : ℕ) := ULift.{u} {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2}

/-- 概要：順序区間の対象。
方針：端点と順序の証明をまとめる。
規約：証明に依存しない。使われ方：対角と四角形の頂点。 -/
def arObj {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : Ar.{u} n := ⟨⟨(i,j),h⟩⟩

/-- 概要：単調写像は区間の両端に作用する。
方針：単調性から端点条件と成分ごとの順序を保つ。
規約：共変。使われ方：S• の反変性。 -/
def arMap {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : Ar.{u} m →o Ar.{u} n where
  toFun a := arObj (θ a.down.val.1) (θ a.down.val.2) (θ.monotone a.down.property)
  monotone' a b h := ⟨θ.monotone h.1, θ.monotone h.2⟩

@[simp] lemma arMap_id (n : ℕ) : arMap.{u} (OrderHom.id : Fin (n + 1) →o _) = OrderHom.id := by
  rfl

@[simp] lemma arMap_comp {l m n : ℕ} (θ : Fin (l + 1) →o Fin (m + 1))
    (φ : Fin (m + 1) →o Fin (n + 1)) : arMap.{u} (φ.comp θ) = (arMap φ).comp (arMap θ) := rfl

/-- 概要：Ar[n] の nerve。
方針：順序圏の通常の nerve を使う。
規約：任意の単体集合の宇宙に取る。使われ方：図式圏の始域。 -/
def arNerve (n : ℕ) : SSet.{u} := nerve (Ar.{u} n)

/-- 概要：単調写像が誘導する nerve の射。
方針：順序関手を nerve に送る。
規約：共変。使われ方：図式の制限。 -/
def arNerveMap {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) :
    arNerve.{u} m ⟶ arNerve.{u} n := nerveMap (arMap θ).toFunctor

@[simp] lemma arNerveMap_id (n : ℕ) :
    arNerveMap.{u} (OrderHom.id : Fin (n + 1) →o _) = 𝟙 _ := rfl

@[simp] lemma arNerveMap_comp {l m n : ℕ} (θ : Fin (l + 1) →o Fin (m + 1))
    (φ : Fin (m + 1) →o Fin (n + 1)) :
    arNerveMap.{u} (φ.comp θ) = arNerveMap θ ≫ arNerveMap φ := rfl

/-- 概要：Ar[n] 型の C 内の図式全体。
方針：単体集合の内部 Hom を使う。
規約：core はまだ取らない。使われ方：gapped の充満部分単体集合。 -/
def diagramSpace (n : ℕ) (C : SSet.{u}) : SSet.{u} := (ihom (arNerve n)).obj C

/-- 概要：順序区間の二端点を結ぶ単調写像。
方針：Fin 2 の二つの場合を使う。
規約：端点は等しくてもよい。使われ方：Ar の四角形。 -/
def intervalStep {n : ℕ} (a b : Fin (n + 1)) (h : a ≤ b) : Fin 2 →o Fin (n + 1) where
  toFun x := if x = 0 then a else b
  monotone' x y hxy := by
    fin_cases x <;> fin_cases y <;> simp_all

lemma intervalStep_le {n : ℕ} (a b : Fin (n + 1)) (h : a ≤ b) (x : Fin 2) :
    intervalStep a b h x ≤ b := by
  change (if x = 0 then a else b) ≤ b
  split <;> simp_all

lemma le_intervalStep {n : ℕ} (a b : Fin (n + 1)) (h : a ≤ b) (x : Fin 2) :
    a ≤ intervalStep a b h x := by
  change a ≤ (if x = 0 then a else b)
  split <;> simp_all

/-- 概要：i≤j≤k≤l の区間で作る Ar[n] の四角形。
方針：横は k→l、縦は i→j とする。
規約：左下 (i,k)、右上 (j,l)。使われ方：gapped の押し出し条件。 -/
def arSquareOrder {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    ULift.{u} (Fin 2 × Fin 2) →o Ar.{u} n where
  toFun x := arObj (intervalStep i j hij x.down.2) (intervalStep k l hkl x.down.1)
    ((intervalStep_le i j hij _).trans (hjk.trans (le_intervalStep k l hkl _)))
  monotone' a b h := ⟨(intervalStep i j hij).monotone h.2,
    (intervalStep k l hkl).monotone h.1⟩

/-- 概要：Ar[n] 内の四角形を単体集合の射にする。
方針：正方形の nerve 表示から順序関手の nerve に写す。
規約：退化する四角形も含む。使われ方：IsPushoutSquare への入力。 -/
def arSquare {n : ℕ} (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve.{u} n :=
  (prodStdSimplex.isoNerve 1 1).hom ≫ nerveMap (arSquareOrder i j k l hij hjk hkl).toFunctor

/-- 概要：gapped 図式は零対角と全区間四角形の押し出し性を持つ。
方針：α-S の零頂点・押し出しの定義を直接用いる。
規約：quasicategory 性や安定性と独立に述語を定義する。
使われ方：BGT Definition 7.1 の S_n(C)。 -/
def IsGapped {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C) : Prop :=
  (∀ i : Fin (n + 1), _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ (arObj i i le_rfl)))) ∧
  ∀ (i j k l : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare i j k l hij hjk hkl ≫ F)

/-- 概要：単調写像は区間四角形と可換。
方針：二端点の選択が写像と可換であることを使う。
規約：端点の順序証明は proof irrelevance による。使われ方：gapped の制限。 -/
lemma arSquare_naturality {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1))
    (i j k l : Fin (m + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    arSquare i j k l hij hjk hkl ≫ arNerveMap.{u} θ =
      arSquare (θ i) (θ j) (θ k) (θ l)
        (θ.monotone hij) (θ.monotone hjk) (θ.monotone hkl) := by
  have he : (arSquareOrder i j k l hij hjk hkl).toFunctor ⋙ (arMap θ).toFunctor =
      (arSquareOrder (θ i) (θ j) (θ k) (θ l)
        (θ.monotone hij) (θ.monotone hjk) (θ.monotone hkl)).toFunctor := by
    refine CategoryTheory.Functor.ext (fun x ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext
    · change θ (if x.down.2 = 0 then i else j) =
        (if x.down.2 = 0 then θ i else θ j)
      split <;> rfl
    · change θ (if x.down.1 = 0 then k else l) =
        (if x.down.1 = 0 then θ k else θ l)
      split <;> rfl
  change (prodStdSimplex.isoNerve 1 1).hom ≫ nerveMap
    (arSquareOrder i j k l hij hjk hkl).toFunctor ≫ nerveMap (arMap θ).toFunctor = _
  change (prodStdSimplex.isoNerve 1 1).hom ≫ nerveMap
    ((arSquareOrder i j k l hij hjk hkl).toFunctor ⋙ (arMap θ).toFunctor) = _
  rw [he]
  rfl

/-- 概要：単調写像による制限は gapped 条件を保つ。
方針：対角と四角形を添字の像で評価する。
規約：安定性の仮定は不要。使われ方：S• の全ての単体作用素。 -/
lemma IsGapped.precomp {m n : ℕ} {C : SSet.{u}} {F : arNerve n ⟶ C}
    (hF : IsGapped F) (θ : Fin (m + 1) →o Fin (n + 1)) :
    IsGapped (arNerveMap θ ≫ F) := by
  constructor
  · intro i
    exact hF.1 (θ i)
  · intro i j k l hij hjk hkl
    rw [← Category.assoc, arSquare_naturality]
    exact hF.2 _ _ _ _ _ _ _

/-- 概要：gapped な関手頂点の張る充満部分単体集合。
方針：内部 Hom の頂点を実際の図式に戻して条件を課す。
規約：core は別工程で取る。使われ方：∞-S• の n 段目。 -/
def gappedSubcomplex (n : ℕ) (C : SSet.{u}) : (diagramSpace n C).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (diagramSpace n C)
    (fun v ↦ IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm v))

/-- 概要：S_n(C) は全 gapped 図式の単体集合。
方針：充満部分複体の underlying 単体集合を取る。
規約：全ての選択を保持する。使われ方：BGT §7 の S•。 -/
def sConstruction (n : ℕ) (C : SSet.{u}) : SSet.{u} := gappedSubcomplex n C

/-- 概要：gapped 図式は quasicategory をなす。
方針：内部 Hom と充満部分複体の quasicategory 性を使う。
規約：C の安定性はまだ不要。使われ方：各段の core。 -/
instance sConstruction_quasicategory (n : ℕ) (C : SSet.{u}) [Quasicategory C] : Quasicategory (sConstruction n C) := by
  dsimp [sConstruction, gappedSubcomplex, diagramSpace]
  infer_instance

/-- 概要：単調写像による gapped 図式の制限。
方針：前合成を全部分複体に持ち上げる。
規約：反変。使われ方：S• の面・退化写像。 -/
def sMap {m n : ℕ} (C : SSet.{u}) (θ : Fin (m + 1) →o Fin (n + 1)) :
    sConstruction n C ⟶ sConstruction m C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((gappedSubcomplex n C).ι ≫ (pre (arNerveMap θ)).app C) (by
    intro v
    let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm v.val
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).apply_symm_apply v.val
    have hF : IsGapped F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m) C).symm
      (((pre (arNerveMap θ)).app C).app (Opposite.op ⦋0⦌) v.val))
    rw [← hv]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m) C).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m) C (arNerveMap θ ≫ F)))
    rw [Equiv.symm_apply_apply]
    exact hF.precomp θ)

/-- 概要：制限の包含後の値は通常の前合成。
方針：充満部分複体の持ち上げの式。
規約：厳密等号。使われ方：単体恒等式。 -/
lemma sMap_ι {m n : ℕ} (C : SSet.{u}) (θ : Fin (m + 1) →o Fin (n + 1)) :
    sMap C θ ≫ (gappedSubcomplex m C).ι =
      (gappedSubcomplex n C).ι ≫ (pre (arNerveMap θ)).app C := rfl

@[simp] lemma sMap_id (n : ℕ) (C : SSet.{u}) :
    sMap C (OrderHom.id : Fin (n + 1) →o _) = 𝟙 (sConstruction n C) := by
  apply (cancel_mono (gappedSubcomplex n C).ι).1
  rw [sMap_ι, arNerveMap_id, pre_id]
  change (gappedSubcomplex n C).ι ≫ 𝟙 _ = 𝟙 _ ≫ (gappedSubcomplex n C).ι
  simp only [Category.comp_id, Category.id_comp]

@[simp] lemma sMap_comp {l m n : ℕ} (C : SSet.{u})
    (θ : Fin (l + 1) →o Fin (m + 1)) (φ : Fin (m + 1) →o Fin (n + 1)) :
    sMap C (φ.comp θ) = sMap C φ ≫ sMap C θ := by
  apply (cancel_mono (gappedSubcomplex l C).ι).1
  rw [sMap_ι, Category.assoc, sMap_ι, ← Category.assoc, sMap_ι]
  rw [arNerveMap_comp, pre_map, NatTrans.comp_app, Category.assoc]

/-- 概要：全 gapped 図式からなる単体的単体集合。
方針：Ar の関手性から反変な制限関手を作る。
規約：core・実現の前の S•C。使われ方：BGT §7 の K 理論。 -/
def simplicialSConstruction (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj n := sConstruction n.unop.len C
  map θ := sMap C θ.unop.toOrderHom
  map_id n := sMap_id n.unop.len C
  map_comp θ φ := sMap_comp C φ.unop.toOrderHom θ.unop.toOrderHom

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Def 7.1"] _root_.SerrePositivity.KST.SConstruction.IsGapped
attribute [cite BGT "Def 7.1"] _root_.SerrePositivity.KST.SConstruction.gappedSubcomplex
attribute [cite HA "1.2.2.2" (partial := special) "仮定：点付き準圏と有限全順序 [n]（Lean が強い：HA の I は任意の全順序）。結論：Ar の対角を零にし、順序付き三点の所定の正方形に押し出しを要求し、その充満部分複体を作る（有限の場合は一致）。"] _root_.SerrePositivity.KST.SConstruction.IsGapped
attribute [cite HA "1.2.2.2" (partial := special) "仮定：点付き準圏と有限全順序 [n]（Lean が強い：HA の I は任意の全順序）。結論：Ar の対角を零にし、順序付き三点の所定の正方形に押し出しを要求し、その充満部分複体を作る（有限の場合は一致）。"] _root_.SerrePositivity.KST.SConstruction.sConstruction
