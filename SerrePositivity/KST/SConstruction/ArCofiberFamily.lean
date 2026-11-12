module
public import SerrePositivity.KST.SConstruction.CofiberRows
public import SerrePositivity.KST.SConstruction.CofiberFamilies

/-! # Ar[n] 上の自然な cofiber 四角形の族
概要：gapped 図式の全ての (0,i)→(0,j) の cofiber 四角形を同時に取り出す。
方針：Ar[n] と正方形の積から Ar[n] への順序写像を使う。
規約：四角形の角は (0,i),(0,j),(i,i),(i,j)。
使われ方：第一行からの相対 cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：二端点をそれぞれ大きくすると同じ時刻の区間の値も大きくなる。
方針：時刻の二つの場合で端点の不等式を使う。
規約：端点の順序証明には依存しない。使われ方：cofiber 四角形の族の順序性。 -/
lemma intervalStep_mono_endpoints {n : ℕ} {a b a' b' : Fin (n + 1)}
    (hab : a ≤ b) (hab' : a' ≤ b') (ha : a ≤ a') (hb : b ≤ b') (x : Fin 2) :
    intervalStep a b hab x ≤ intervalStep a' b' hab' x := by
  change (if x = 0 then a else b) ≤ (if x = 0 then a' else b')
  split
  · exact ha
  · exact hb

/-- 概要：区間 (i,j) に付随する cofiber 四角形の角を返す順序写像。
方針：横は i→j、縦は 0→i とし、端点と時刻の単調性を合わせる。
規約：右上角は元の区間。使われ方：Ar[n] 上の普遍的な四角形の族。 -/
def arCofiberSquareOrder (n : ℕ) : Ar.{u} n × ULift.{u} (Fin 2 × Fin 2) →o Ar.{u} n where
  toFun p := arObj
    (intervalStep 0 p.1.down.val.1 (Fin.zero_le _) p.2.down.2)
    (intervalStep p.1.down.val.1 p.1.down.val.2 p.1.down.property p.2.down.1)
    ((intervalStep_le 0 p.1.down.val.1 (Fin.zero_le _) _).trans
      (le_intervalStep p.1.down.val.1 p.1.down.val.2 p.1.down.property _))
  monotone' a b h := by
    constructor
    · exact ((intervalStep 0 a.1.down.val.1 (Fin.zero_le _)).monotone h.2.2).trans
        (intervalStep_mono_endpoints _ _ le_rfl h.1.1 _)
    · exact ((intervalStep a.1.down.val.1 a.1.down.val.2 a.1.down.property).monotone h.2.1).trans
        (intervalStep_mono_endpoints _ _ h.1.1 h.1.2 _)

/-- 概要：Ar[n] の鎖と正方形の単体を、cofiber 四角形の鎖へ写す。
方針：同じ頂点番号で二つの鎖を合わせて順序写像を適用する。
規約：次数 d の実際の鎖。使われ方：四角形の族の単体作用。 -/
def arCofiberSquareChain {n d : ℕ}
    (s : (arNerve.{u} n ⊗ (Δ[1] ⊗ Δ[1] : SSet.{u})) _⦋d⦌) : ComposableArrows (Ar.{u} n) d :=
  (show Monotone (fun r : Fin (d + 1) ↦
    arCofiberSquareOrder n
      (s.1.obj r, (ULift.up (prodStdSimplex.objEquiv s.2 r) : ULift.{u} (Fin 2 × Fin 2)))) from by
      intro r t h
      exact (arCofiberSquareOrder n).monotone
        ⟨s.1.monotone h, (prodStdSimplex.objEquiv s.2).monotone h⟩).functor

/-- 概要：Ar[n] と正方形の積から cofiber 四角形の角へ写す単体集合の射。
方針：鎖の頂点ごとの構成は前合成と厳密に可換。
規約：Ar[n] が第一因子。使われ方：gapped 図式から cofiber の族を取り出す。 -/
def arCofiberSquareMap (n : ℕ) : arNerve.{u} n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n where
  app d := ↾fun s ↦ arCofiberSquareChain s
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    rfl

/-- 概要：四角形の族を一つの区間 (i,j) で評価すると対応する cofiber 四角形。
方針：鎖ごとの二端点選択を計算する。
規約：零対角の四角形も含む。使われ方：各頂点の cofiber 条件。 -/
lemma arCofiberSquareMap_at {n : ℕ} (a : Ar.{u} n) :
    ((CartesianMonoidalCategory.lift
      (SSet.const (ComposableArrows.mk₀ a)) (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u}))) ≫ arCofiberSquareMap n) =
      arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  rfl

/-- 概要：curry した族を頂点で評価すると、その頂点で制限した関手の頂点表示。
方針：単位からの射の curry と uncurry の逆律を使う。
規約：任意の単体集合で成立。使われ方：Ar 上の cofiber 四角形の頂点計算。 -/
lemma curry_vertex_value {A B C : SSet.{u}} (H : B ⊗ A ⟶ C) (a : A _⦋0⦌) :
    (curry H).app (Opposite.op ⦋0⦌) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (CartesianMonoidalCategory.lift (𝟙 B) (SSet.const a) ≫ H) := by
  have hh : CartesianMonoidalCategory.lift (𝟙 B) (SSet.const a) ≫ H =
      uncurry' ((SSet.unitHomEquiv A).symm a ≫ curry H) := by
    rw [uncurry', uncurry_natural_left, uncurry_curry]
    rfl
  rw [hh]
  change _ = SSet.unitHomEquiv _ (curry' (uncurry' ((SSet.unitHomEquiv A).symm a ≫ curry H)))
  rw [curry'_uncurry']
  change (curry H).app (Opposite.op ⦋0⦌) a =
    (curry H).app (Opposite.op ⦋0⦌)
      (A.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op a)
  have h0 : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
  rw [h0, op_id, CategoryTheory.Functor.map_id_apply]

/-- 概要：Ar[n] の図式から全区間の cofiber 四角形の族を取り出す。
方針：自然な正方形の族で制限して curry する。
規約：この定義では gapped 条件を要求しない。使われ方：第一行からの復元の逆方向。 -/
def arCofiberFamily {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C) :
    arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  curry ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom ≫ arCofiberSquareMap n ≫ F)

/-- 概要：cofiber 四角形の族の (i,j) 成分は対応する cofiber 四角形。
方針：curry の頂点評価と添字写像の評価を合わせる。
規約：実際の射の関手頂点による等号。使われ方：族の普遍性を頂点で判定する。 -/
lemma arCofiberFamily_vertex {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C) (a : Ar.{u} n) :
    (arCofiberFamily F).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2
        (Fin.zero_le _) le_rfl a.down.property ≫ F) := by
  rw [arCofiberFamily, curry_vertex_value]
  apply congrArg (fun f : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  have he : CartesianMonoidalCategory.lift (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u}))
      (SSet.const (ComposableArrows.mk₀ a)) ≫
      (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom =
        CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a))
          (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) := rfl
  rw [← Category.assoc, ← Category.assoc, he, arCofiberSquareMap_at]

/-- 概要：gapped 図式の各区間は同時に cofiber 四角形の族をなす。
方針：全頂点で零対角と押し出し条件を確認し、充満部分複体に持ち上げる。
規約：C の quasicategory 性・安定性は不要。使われ方：既存の gapped 境界の cofiber 補完。 -/
def gappedCofiberFamily {n : ℕ} {C : SSet.{u}} {F : arNerve n ⟶ C} (hF : IsGapped F) :
    arNerve n ⟶ cofiberDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (arCofiberFamily F) (by
    intro v
    obtain ⟨a, rfl⟩ := nerveEquiv.symm.surjective v
    change IsCofiberDiagramVertex ((arCofiberFamily F).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a))
    rw [arCofiberFamily_vertex]
    constructor
    · rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex, arSquare_cofiber_zero_corner]
      exact hF.1 _
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C (arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2
          (Fin.zero_le _) le_rfl a.down.property ≫ F)))
      rw [Equiv.symm_apply_apply]
      exact hF.2 _ _ _ _ _ _ _)

/-- 概要：curry した族の指定頂点での評価はその頂点を第一因子に固定した射。
方針：内部 Hom の評価を各次数で計算する。
規約：任意の単体集合。使われ方：cofiber 四角形の頂点の回収。 -/
lemma curry_evaluate_vertex {A B C : SSet.{u}} (H : B ⊗ A ⟶ C) (b : B _⦋0⦌) :
    curry H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b =
      CartesianMonoidalCategory.lift (SSet.const b) (𝟙 A) ≫ H := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  change H.app (Opposite.op ⦋d⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b d, A.map (𝟙 _) a) = _
  rw [CategoryTheory.Functor.map_id_apply]
  rfl

/-- 概要：cofiber 四角形の族の右上角は元の Ar[n] の区間。
方針：端点の選択で横・縦とも時刻一を取る。
規約：図式を入れる前の添字の厳密等号。使われ方：元の図式の回収。 -/
lemma arCofiberSquareMap_apex (n : ℕ) :
    CartesianMonoidalCategory.lift (𝟙 (arNerve.{u} n))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ arCofiberSquareMap n = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> rfl

/-- 概要：自然な cofiber 四角形の族の右上角を取ると元の図式に戻る。
方針：curry の評価と添字の右上角の恒等式を合わせる。
規約：gapped 条件は不要。使われ方：復元した cofiber 族の境界の厳密化。 -/
lemma arCofiberFamily_apex {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C) :
    arCofiberFamily F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = F := by
  rw [arCofiberFamily, curry_evaluate_vertex]
  have he : CartesianMonoidalCategory.lift
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (𝟙 (arNerve n)) ≫ (β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom =
      CartesianMonoidalCategory.lift (𝟙 (arNerve n))
        (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
          stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := rfl
  rw [← Category.assoc, ← Category.assoc, he, arCofiberSquareMap_apex, Category.id_comp]

/-- 概要：cofiber 四角形の右上角を取る。
方針：全部分複体の包含の後で頂点 (1,1) を評価する。
規約：安定性は定義に不要。使われ方：補完した族から Ar 図式を取り出す。 -/
def cofiberApex (C : SSet.{u}) : cofiberDiagrams C ⟶ C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 概要：gapped 図式を cofiber 族にして右上角を取ると元の図式。
方針：充満部分複体の持ち上げと右上角の評価式を使う。
規約：厳密な回収の等号。使われ方：相対補完の指定境界の回収。 -/
lemma gappedCofiberFamily_apex {n : ℕ} {C : SSet.{u}} {F : arNerve n ⟶ C} (hF : IsGapped F) :
    gappedCofiberFamily hF ≫ cofiberApex C = F := by
  change (gappedCofiberFamily hF ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
      stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = F
  change arCofiberFamily F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = F
  exact arCofiberFamily_apex F

end SerrePositivity.KST.SConstruction
