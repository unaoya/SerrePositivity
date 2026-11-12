module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PathMaximum

/-!
概要：豊穣 Hom の単体を右 pinched な coherent nerve の単体へ送る。
方針：最後の頂点だけを終域に写し、そこへ至る Hom は path の最大元で単体を評価する。
規約：Mathlib の包含順序の規約を用いる。局所 Kan 性は仮定しない。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、Remark 4.6.7.9（Tag 01LH） の向きを調整した比較写像。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- 概要：豊穣恒等を左から合成しても単体は変わらない。
方針：豊穣圏の左単位則を各単体で評価する。
規約：次数 d は任意。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の豊穣関手の合成則。 -/
lemma simplicialHom_id_comp_app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) (d : SimplexCategoryᵒᵖ) (a : (SimplicialCategory.sHom X Y).obj d) :
    (eComp SSet X X Y).app d ((eId SSet X).app d PUnit.unit, a) = a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (e_id_comp SSet X Y) d) a

/-- 概要：豊穣恒等を右から合成しても単体は変わらない。
方針：豊穣圏の右単位則を各単体で評価する。
規約：次数 d は任意。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の豊穣関手の合成則。 -/
lemma simplicialHom_comp_id_app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) (d : SimplexCategoryᵒᵖ) (a : (SimplicialCategory.sHom X Y).obj d) :
    (eComp SSet X Y Y).app d (a, (eId SSet Y).app d PUnit.unit) = a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (e_comp_id SSet X Y) d) a

/-- 概要：同じ端点から同じ端点への path は恒等 path。
方針：path の各点を端点で上下から挟む。
規約：任意の線形順序集合で成立する。
使われ方：Kerodon §2.4.3（Tag 00KM）、比較の恒等 Hom 上の計算。 -/
lemma thickeningPath_end_eq_id {J : Type u} [LinearOrder J] (a : J) (P : Path a a) :
    P = 𝟙 (⟨a⟩ : SimplicialThickening J) := by
  apply SimplicialThickening.Path.ext
  ext k
  change k ∈ P.I ↔ k = a
  constructor
  · intro hk
    exact le_antisymm (P.le_right k hk) (P.left_le k hk)
  · rintro rfl
    exact P.left

/-- 概要：終点上の自己 Hom の単体を右から合成しても元の Hom の単体は変わらない。
方針：自己 path の各頂点を恒等に直し、関手の対象上で合成則を使う。
規約：simplicial thickening の豊穣合成を各次数で比較する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、終域側の恒等 Hom の合成。 -/
lemma thickeningHom_comp_end_right {J : Type u} [LinearOrder J]
    (i j : SimplicialThickening J) (d : SimplexCategoryᵒᵖ)
    (P : (SimplicialCategory.sHom i j).obj d) (Q : (SimplicialCategory.sHom j j).obj d) :
    (eComp SSet i j j).app d (P, Q) = P := by
  apply CategoryTheory.Functor.ext (fun k ↦ ?_)
  change (P.obj k ≫ Q.obj k) = P.obj k
  have hQ : Q.obj k = 𝟙 j := thickeningPath_end_eq_id j.as (Q.obj k)
  rw [hQ, Category.comp_id]

/-- 概要：最大元による Hom の座標は path の前半の合成を無視する。
方針：標準単体の頂点で最大元の合成則を使う。
規約：前半の二端点は最後の頂点より前にある。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の豊穣合成則の非定値部分。 -/
lemma pathLastMaximumMap_comp {n : ℕ} (i j : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (P : (nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc))).obj d)
    (Q : (nerve (Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))).obj d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d
      ((eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩).app d (P, Q)) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j).app d Q := by
  apply stdSimplex.ext
  intro k
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply i _ k).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_comp (P.obj k) (Q.obj k)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply j Q k).symm)

/-- 概要：比較の豊穣図式の対象の作用。
方針：最後の頂点を Y、それより前の全頂点を X に写す。
規約：n 単体の Hom の比較では頂点数は n+2。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、右 pinched な図式の二つの対象。 -/
def coherentHomComparisonObj {C : Type v} (X Y : C) {n : ℕ} (i : Fin (n + 2)) : C :=
  Fin.lastCases Y (fun _ ↦ X) i

/-- 概要：比較の図式は最後の頂点を終域へ送る。
方針：対象の分岐の最後の場合を計算する。
規約：最後の頂点は Fin.last (n+1)。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、豊穣関手の端点の計算。 -/
lemma coherentHomComparisonObj_last {C : Type v} (X Y : C) (n : ℕ) :
    coherentHomComparisonObj X Y (Fin.last (n + 1)) = Y := by
  simp only [coherentHomComparisonObj, Fin.lastCases_last]

/-- 概要：比較の図式は最後以外の頂点を始域へ送る。
方針：対象の分岐の castSucc の場合を計算する。
規約：元の n 単体の頂点を castSucc で含める。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、定値な先頭面の計算。 -/
lemma coherentHomComparisonObj_cast {C : Type v} (X Y : C) {n : ℕ} (i : Fin (n + 1)) :
    coherentHomComparisonObj X Y i.castSucc = X := by
  simp only [coherentHomComparisonObj, Fin.lastCases_castSucc]

/-- 概要：最後の頂点から前の頂点への空の Hom からの射。
方針：入力単体に含まれる path の順序条件の矛盾を使う。
規約：標的は任意の単体集合。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、逆向きの Hom の空性。 -/
def coherentHomEmptyMap {n : ℕ} (j : Fin (n + 1)) (Z : SSet.{u}) :
    nerve (Path (ULift.up (Fin.last (n + 1)) : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc)) ⟶ Z where
  app d := ↾fun P ↦ False.elim (by
    have h := Path.le (P.obj 0)
    change Fin.last (n + 1) ≤ j.castSucc at h
    have := j.isLt
    change n + 1 ≤ j.val at h
    omega)
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change Fin.last (n + 1) ≤ j.castSucc at h
    have := j.isLt
    change n + 1 ≤ j.val at h
    omega

/-- 概要：Hom の単体が定める比較の Hom 上の作用。
方針：非定値部分は最大元の射で単体を評価し、同じ対象の間は恒等に写す。
規約：最後の頂点から前へ向かう空の Hom も含めて定義する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の豊穣関手のデータ。 -/
noncomputable def coherentHomComparisonHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
      SimplicialCategory.sHom (coherentHomComparisonObj X Y i)
        (coherentHomComparisonObj X Y j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [coherentHomComparisonObj, Fin.lastCases_last]
      exact toUnit _ ≫ eId SSet Y
    | cast j =>
      simp only [coherentHomComparisonObj, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact coherentHomEmptyMap j _
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [coherentHomComparisonObj, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ
    | cast j =>
      simp only [coherentHomComparisonObj, Fin.lastCases_castSucc]
      exact toUnit _ ≫ eId SSet X

/-- 概要：対象の等号による Hom の移送は豊穣恒等を保つ。
方針：対象の等号を消去して恒等の計算に帰着する。
規約：等号 A=X に沿って X の恒等を A の Hom に移す。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、終域の分岐に伴う単位則。 -/
lemma simplicialHom_id_transport {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A X : C} (h : A = X) (d : SimplexCategoryᵒᵖ) :
    (eId SSet A).app d PUnit.unit =
      (eqToHom (congrArg₂ SimplicialCategory.sHom h h).symm).app d
        ((eId SSet X).app d PUnit.unit) := by
  subst A
  rfl

/-- 概要：豊穣 Hom の端点を等号で移す操作は豊穣合成と整合する。
方針：三つの対象の等号を消去して恒等射の合成に帰着する。
規約：順方向の等号 A=X に対し Hom の単体は逆向きに移す。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の対象の分岐に伴う Hom の移送。 -/
lemma simplicialHom_comp_transport {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B D X Y Z : C} (hA : A = X) (hB : B = Y) (hD : D = Z)
    (d : SimplexCategoryᵒᵖ) (a : (SimplicialCategory.sHom X Y).obj d)
    (b : (SimplicialCategory.sHom Y Z).obj d) :
    (eComp SSet A B D).app d
      ((eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d a,
       (eqToHom (congrArg₂ SimplicialCategory.sHom hB hD).symm).app d b) =
      (eqToHom (congrArg₂ SimplicialCategory.sHom hA hD).symm).app d
        ((eComp SSet X Y Z).app d (a, b)) := by
  subst A
  subst B
  subst D
  rfl

/-- 概要：豊穣 Hom の n 単体から作る coherent nerve の (n+1) 単体。
方針：最大元で評価する Hom の作用を、単位則と path の合成則で豊穣関手にする。
規約：最初の n+1 頂点を X、最後の頂点を Y に写す。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、右 pinched 比較の各単体。 -/
noncomputable def coherentHomComparisonSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) : (SimplicialNerve C) _⦋n + 1⦌ where
  obj i := coherentHomComparisonObj X Y i.as.down
  map i j := coherentHomComparisonHom σ i.as.down j.as.down
  map_id := by
    rintro ⟨⟨i⟩⟩
    induction i using Fin.lastCases
    all_goals
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      simp -implicitDefEqProofs +instances [coherentHomComparisonHom,
        coherentHomComparisonObj_last, coherentHomComparisonObj_cast]
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      induction k using Fin.lastCases
    all_goals
      simp -implicitDefEqProofs +instances only [coherentHomComparisonHom, eq_mpr_eq_cast,
        coherentHomComparisonObj_last, congrArg_cast_hom_right, Category.assoc,
        eqToHom_naturality, eqToHom_refl, Category.id_comp, coherentHomComparisonObj_cast,
        Fin.lastCases_last, Fin.lastCases_castSucc, comp_toUnit_assoc]
      repeat' first
        | erw [coherentHomComparisonObj_last X Y n]
        | erw [coherentHomComparisonObj_cast X Y (n := n)]
      try simp only [eqToHom_refl, Category.comp_id]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      rintro ⟨P, Q⟩
    case last.last.last =>
      change (eId SSet Y).app d PUnit.unit =
        (eComp SSet Y Y Y).app d ((eId SSet Y).app d PUnit.unit,
          (eId SSet Y).app d PUnit.unit)
      exact (simplicialHom_id_comp_app Y Y d _).symm
    case last.last.cast k =>
      have h := SimplicialThickening.Path.le (Q.obj 0)
      change n + 1 ≤ k.val at h
      have : k.val < n + 1 := k.isLt
      omega
    case last.cast.last j =>
      have h := SimplicialThickening.Path.le (P.obj 0)
      change n + 1 ≤ j.val at h
      have : j.val < n + 1 := j.isLt
      omega
    case last.cast.cast j k =>
      have h := SimplicialThickening.Path.le (P.obj 0)
      change n + 1 ≤ j.val at h
      have : j.val < n + 1 := j.isLt
      omega
    case cast.last.cast i k =>
      have h := SimplicialThickening.Path.le (Q.obj 0)
      change n + 1 ≤ k.val at h
      have : k.val < n + 1 := k.isLt
      omega
    case cast.last.last i =>
      let hA := coherentHomComparisonObj_cast X Y (n := n) i
      let hB := coherentHomComparisonObj_last X Y n
      let R := (eComp SSet
        (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up (Fin.last (n + 1))⟩ ⟨ULift.up (Fin.last (n + 1))⟩).app d (P, Q)
      let f := (SSet.yonedaEquiv.symm σ).app d
      let a := f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d P)
      change (eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d
        (f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d R)) =
          (eComp SSet _ _ _).app d
            ((eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d a,
             (eId SSet (coherentHomComparisonObj X Y (Fin.last (n + 1)))).app d PUnit.unit)
      rw [simplicialHom_id_transport hB, simplicialHom_comp_transport hA hB hB]
      have hR : R = P := thickeningHom_comp_end_right _ _ d P Q
      rw [hR, simplicialHom_comp_id_app]
    case cast.cast.last i j =>
      let hA := coherentHomComparisonObj_cast X Y (n := n) i
      let hB := coherentHomComparisonObj_cast X Y (n := n) j
      let hD := coherentHomComparisonObj_last X Y n
      let R := (eComp SSet
        (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩).app d (P, Q)
      let f := (SSet.yonedaEquiv.symm σ).app d
      let a := f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j).app d Q)
      change (eqToHom (congrArg₂ SimplicialCategory.sHom hA hD).symm).app d
        (f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d R)) =
          (eComp SSet _ _ _).app d
            ((eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d
               ((eId SSet X).app d PUnit.unit),
             (eqToHom (congrArg₂ SimplicialCategory.sHom hB hD).symm).app d a)
      rw [simplicialHom_comp_transport hA hB hD]
      rw [simplicialHom_id_comp_app]
      exact congrArg (fun t ↦
        (eqToHom (congrArg₂ SimplicialCategory.sHom hA hD).symm).app d (f t))
          (pathLastMaximumMap_comp i j d P Q)
    case cast.cast.cast i j k =>
      let hA := coherentHomComparisonObj_cast X Y (n := n) i
      let hB := coherentHomComparisonObj_cast X Y (n := n) j
      let hD := coherentHomComparisonObj_cast X Y (n := n) k
      change (eqToHom (congrArg₂ SimplicialCategory.sHom hA hD).symm).app d
        ((eId SSet X).app d PUnit.unit) =
          (eComp SSet _ _ _).app d
            ((eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d
              ((eId SSet X).app d PUnit.unit),
             (eqToHom (congrArg₂ SimplicialCategory.sHom hB hD).symm).app d
              ((eId SSet X).app d PUnit.unit))
      rw [simplicialHom_comp_transport hA hB hD, simplicialHom_id_comp_app]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
