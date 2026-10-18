module
public import SerrePositivity.KST.SConstruction.DiagonalReduction
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! # 単体的図式の各段から対角実現への組み立て
概要：Δ[m] と m 次段の積から対角実現へ写し、次数変更・入力への自然性を証明する。
方針：n 単体の α:[n]→[m] に外側の反変構造写像を適用する。
規約：幾何的実現を別に導入しない。使われ方：反復 S の suspension 構造射の降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 概要：単体とその次数の図式から対角実現を組み立てる。
方針：α:[n]→[m] の反対による外側の構造射を n 次単体に適用する。
規約：任意の単体的単体集合に適用する。使われ方：構造射の cylinder。 -/
def diagonalAssembly (m : ℕ) (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (Δ[m] : SSet.{u}) ⊗ X.obj (Opposite.op ⦋m⦌) ⟶ simplicialDiagonalFunctor.obj X where
  app d := ↾fun z => (X.map (stdSimplex.objEquiv z.1).op).app d z.2
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro z
    symm
    change (X.obj e).map f
        (((X.map (stdSimplex.objEquiv z.1).op ≫ X.map f).app d) z.2) =
      (X.map (f.unop ≫ stdSimplex.objEquiv z.1).op).app e
        ((X.obj (Opposite.op ⦋m⦌)).map f z.2)
    rw [← X.map_comp]
    exact ConcreteCategory.congr_hom
      ((X.map (f.unop ≫ stdSimplex.objEquiv z.1).op).naturality f).symm z.2

/-- 概要：組み立ては入力の単体的写像について自然。
方針：α に関する自然性を各次数で評価する。
規約：厳密な等号。使われ方：構造射の関手性。 -/
lemma diagonalAssembly_naturality (m : ℕ) {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : X ⟶ Y) :
    ((Δ[m] : SSet.{u}) ◁ f.app (Opposite.op ⦋m⦌)) ≫ diagonalAssembly m Y =
      diagonalAssembly m X ≫ simplicialDiagonalFunctor.map f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (f.naturality (stdSimplex.objEquiv z.1).op) d).symm z.2

/-- 概要：組み立ては外側の次数変更と両立する。
方針：標準単体の後合成と外側の反変関手の合成則を比較する。
規約：全ての単体作用素を含む。使われ方：端点・境界の制御。 -/
lemma diagonalAssembly_reindex {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (stdSimplex.map θ ▷ X.obj (Opposite.op ⦋n⦌)) ≫ diagonalAssembly n X =
      ((Δ[m] : SSet.{u}) ◁ X.map θ.op) ≫ diagonalAssembly m X := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  change (X.map (stdSimplex.objEquiv z.1 ≫ θ).op).app d z.2 =
    ((X.map θ.op ≫ X.map (stdSimplex.objEquiv z.1).op).app d) z.2
  rw [← X.map_comp]
  rfl

/-- 概要：零次段の組み立ては零段の対角への包含。
方針：[n]→[0] の一意性を使う。
規約：Δ[0] の因子は射影で忘れる。使われ方：端点の零段への分解。 -/
lemma diagonalAssembly_zero (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalAssembly 0 X =
      snd (Δ[0] : SSet.{u}) (X.obj (Opposite.op ⦋0⦌)) ≫ diagonalZeroColumn X := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  change (X.map (stdSimplex.objEquiv z.1).op).app d z.2 =
    (X.map (SimplexCategory.const d.unop ⦋0⦌ 0).op).app d z.2
  have he : stdSimplex.objEquiv z.1 = SimplexCategory.const d.unop ⦋0⦌ 0 :=
    Subsingleton.elim _ _
  rw [he]

/-- 概要：任意の頂点における組み立ての端は零段を経由する。
方針：次数変更と零次の組み立ての式を合成する。
規約：頂点は射 [0]→[m] として指定する。使われ方：境界を潰す条件。 -/
lemma diagonalAssembly_endpoint (m : ℕ) (θ : ⦋0⦌ ⟶ ⦋m⦌)
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (stdSimplex.map θ ▷ X.obj (Opposite.op ⦋m⦌)) ≫ diagonalAssembly m X =
      ((Δ[0] : SSet.{u}) ◁ X.map θ.op) ≫
        snd (Δ[0] : SSet.{u}) (X.obj (Opposite.op ⦋0⦌)) ≫ diagonalZeroColumn X := by
  rw [diagonalAssembly_reindex, diagonalAssembly_zero]

/-- 概要：零段を潰すと組み立ての全端点は基点になる。
方針：端点の零段への分解に cofiber の関係式を適用する。
規約：全次数で厳密に基点へ写る。使われ方：円からの構造射への降下条件。 -/
lemma diagonalAssembly_endpoint_reduced (m : ℕ) (θ : ⦋0⦌ ⟶ ⦋m⦌)
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (stdSimplex.map θ ▷ X.obj (Opposite.op ⦋m⦌)) ≫ diagonalAssembly m X ≫
        diagonalReductionQuotient X =
      toUnit ((Δ[0] : SSet.{u}) ⊗ X.obj (Opposite.op ⦋m⦌)) ≫ (reducedDiagonal X).hom := by
  rw [← Category.assoc, diagonalAssembly_endpoint, Category.assoc, Category.assoc]
  change _ ≫ _ ≫ (diagonalZeroColumn X ≫
    PointedObject.cofiberQuotient (diagonalZeroColumn X)) = _
  rw [PointedObject.cofiberQuotient_condition, comp_toUnit_assoc, comp_toUnit_assoc]
  rfl

/-- 概要：区間の境界の任意の単体は定値。
方針：二つの頂点の一方を避ける写像の値は全て一致する。
規約：空でない各単体次数。使われ方：区間の全境界を潰す条件。 -/
lemma intervalBoundary_simplex_constant {n : ℕ} (a : (Δ[1] : SSet.{u}) _⦋n⦌)
    (ha : a ∈ (boundary 1).obj (Opposite.op ⦋n⦌)) :
    stdSimplex.objEquiv a = SimplexCategory.const ⦋n⦌ ⦋1⦌ (a 0) := by
  obtain ⟨j, hj⟩ := (mem_boundary_iff_notMem_range a).1 ha
  have hne (k : Fin (n + 1)) : a k ≠ j := fun h => hj ⟨k, h⟩
  have aux (p q j : Fin 2) (hp : p ≠ j) (hq : q ≠ j) : p = q := by
    fin_cases p <;> fin_cases q <;> fin_cases j <;> simp_all
  ext k
  exact congrArg Fin.val (aux (a k) (a 0) j (hne k) (hne 0))

/-- 概要：区間の全境界は零段を潰した対角の基点へ写る。
方針：境界単体の定値性と各端点の式を使う。
規約：高次の退化単体も含む。使われ方：区間商からの構造射。 -/
lemma diagonalAssembly_interval_boundary (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ≫ diagonalAssembly 1 X ≫
        diagonalReductionQuotient X =
      toUnit ((boundary 1 : (Δ[1] : SSet.{u}).Subcomplex).toSSet ⊗
        X.obj (Opposite.op ⦋1⦌)) ≫ (reducedDiagonal X).hom := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  let a : (Δ[1] : SSet.{u}).obj d := z.1.val
  let θ : ⦋0⦌ ⟶ ⦋1⦌ :=
    SimplexCategory.const ⦋0⦌ ⦋1⦌ ((stdSimplex.objEquiv a).toOrderHom 0)
  let b : ((Δ[0] : SSet.{u}) ⊗ X.obj (Opposite.op ⦋1⦌)).obj d :=
    (stdSimplex.objEquiv.symm (SimplexCategory.const d.unop ⦋0⦌ 0), z.2)
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (diagonalAssembly_endpoint_reduced 1 θ X) d) b
  have he := intervalBoundary_simplex_constant a z.1.property
  change (diagonalReductionQuotient X).app d
      ((X.map (stdSimplex.objEquiv a).op).app d z.2) = _
  rw [he]
  exact h

/-- 概要：区間両端をまとめて潰した一次段から、零段を潰した対角への点つき写像。
方針：区間境界の式を cofiber の普遍性に渡す。
規約：源では全両端を一つの基点にする。使われ方：suspension 構造射の基本比較。 -/
def diagonalIntervalComparison (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    PointedObject.cofiber ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ⟶
      reducedDiagonal X :=
  PointedObject.cofiberDesc _ _ (diagonalAssembly 1 X ≫ diagonalReductionQuotient X)
    (diagonalAssembly_interval_boundary X)

/-- 概要：区間商からの比較は元の組み立てを回収する。
方針：cofiber の降下の関係式。
規約：厳密等号。使われ方：構造射の比較の自然性。 -/
lemma diagonalIntervalComparison_quotient (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    PointedObject.cofiberQuotient ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ≫
      (diagonalIntervalComparison X).right =
        diagonalAssembly 1 X ≫ diagonalReductionQuotient X :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：一次段の区間商の入力に関する写像。
方針：区間の因子を固定して写し、両端を潰す商へ降ろす。
規約：基点を厳密に保存する。使われ方：区間比較の自然性。 -/
def diagonalIntervalMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) :
    PointedObject.cofiber ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ⟶
      PointedObject.cofiber ((boundary 1).ι ▷ Y.obj (Opposite.op ⦋1⦌)) :=
  PointedObject.cofiberDesc _ _
    (((Δ[1] : SSet.{u}) ◁ f.app (Opposite.op ⦋1⦌)) ≫
      PointedObject.cofiberQuotient ((boundary 1).ι ▷ Y.obj (Opposite.op ⦋1⦌))) (by
    rw [← whisker_exchange_assoc, PointedObject.cofiberQuotient_condition,
      comp_toUnit_assoc])

/-- 概要：区間商の写像を元の区間へ引き戻した式。
方針：cofiber の普遍性。
規約：全高次単体の等号。使われ方：関手法則と比較の自然性。 -/
lemma diagonalIntervalMap_quotient {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) :
    PointedObject.cofiberQuotient ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌)) ≫
      (diagonalIntervalMap f).right =
        ((Δ[1] : SSet.{u}) ◁ f.app (Opposite.op ⦋1⦌)) ≫
          PointedObject.cofiberQuotient ((boundary 1).ι ▷ Y.obj (Opposite.op ⦋1⦌)) :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：一次段の区間商は単体的図式について関手。
方針：商への射影と合成して関手法則を検証する。
規約：両端を同一の基点へ潰す。使われ方：反復 S の構造射の源の自然性。 -/
def diagonalIntervalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ PointedSimplicialSet.{u} where
  obj X := PointedObject.cofiber ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌))
  map := diagonalIntervalMap
  map_id X := by
    apply PointedObject.cofiber_hom_ext ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌))
    rw [diagonalIntervalMap_quotient]
    simp
  map_comp {X Y Z} f g := by
    apply PointedObject.cofiber_hom_ext ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌))
    change _ = _ ≫ (diagonalIntervalMap f).right ≫ (diagonalIntervalMap g).right
    rw [diagonalIntervalMap_quotient, ← Category.assoc,
      diagonalIntervalMap_quotient, Category.assoc, diagonalIntervalMap_quotient]
    simp only [NatTrans.comp_app, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- 概要：区間商から零段を潰した対角への比較は入力について自然。
方針：商の射影で検出し、組み立てと零段商の自然性を使う。
規約：基点を含む厳密な自然変換。使われ方：構造射の自然性の基本式。 -/
def diagonalIntervalComparisonNat : diagonalIntervalFunctor ⟶ reducedDiagonalFunctor where
  app := diagonalIntervalComparison
  naturality {X Y} f := by
    apply PointedObject.cofiber_hom_ext ((boundary 1).ι ▷ X.obj (Opposite.op ⦋1⦌))
    change _ ≫ (diagonalIntervalMap f).right ≫ (diagonalIntervalComparison Y).right =
      _ ≫ (diagonalIntervalComparison X).right ≫ (reducedDiagonalMap f).right
    rw [← Category.assoc, diagonalIntervalMap_quotient, Category.assoc,
      diagonalIntervalComparison_quotient, ← Category.assoc,
      diagonalAssembly_naturality, Category.assoc,
      ← reducedDiagonalMap_quotient, ← Category.assoc, ← Category.assoc,
      diagonalIntervalComparison_quotient]

end SerrePositivity.KST.SConstruction
