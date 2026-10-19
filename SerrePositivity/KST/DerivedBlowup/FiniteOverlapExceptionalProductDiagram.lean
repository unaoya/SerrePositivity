module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalProductIso

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の共通 Ko(A;a) 表示を全有限重なりの図式にする。
方針：指定局所 dg 代数同型で既存の例外因子遷移を共役し、自然同型を構成する。
規約：この段階の遷移の定義は共役。標準の係数変更との一致は別に計算する。
使われ方：局所同定を図式全体の比較に組み合わせる。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：共通 Koszul 表示の間の指定遷移。
方針：元の例外因子遷移を指定局所代数同型で共役する。
規約：KST Lemma 3.6。使われ方：共通表示の全有限重なり関手の射。 -/
def finiteOverlapExceptionalProductMap (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) :
    finiteOverlapExceptionalProductAlgebra R a i T ⟶
      finiteOverlapExceptionalProductAlgebra R a k U :=
  (finiteOverlapExceptionalProductIso R a i T).inv ≫
    finiteOverlapExceptionalDGAlgebraMap R a i k h hi ≫
      (finiteOverlapExceptionalProductIso R a k U).hom

/-- 概要：共通 Koszul 表示の遷移は合成を保つ。
方針：中間同型を消去し、実際の例外因子遷移の合成則を使う。
規約：KST Lemma 3.6。使われ方：共通表示の係数関手の合成律。 -/
theorem finiteOverlapExceptionalProductMap_comp (a : I → R) (i k l : I)
    {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    finiteOverlapExceptionalProductMap R a i k h hi ≫
        finiteOverlapExceptionalProductMap R a k l g hk =
      finiteOverlapExceptionalProductMap R a i l (h.trans g) hi := by
  simpa only [finiteOverlapExceptionalProductMap, Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun f => (finiteOverlapExceptionalProductIso R a i T).inv ≫ f ≫
      (finiteOverlapExceptionalProductIso R a l V).hom)
      (finiteOverlapExceptionalDGAlgebraMap_comp R a i k l h g hi hk)

/-- 概要：共通 Koszul 表示の恒等遷移は恒等。
方針：例外因子遷移の恒等律と指定同型の逆を消去する。
規約：KST Lemma 3.6。使われ方：共通表示の係数関手の単位条件。 -/
theorem finiteOverlapExceptionalProductMap_id (a : I → R) (i : I)
    (T : Finset I) (hi : i ∈ T) :
    finiteOverlapExceptionalProductMap R a i i (Finset.Subset.refl T) hi = 𝟙 _ := by
  simp only [finiteOverlapExceptionalProductMap, finiteOverlapExceptionalDGAlgebraMap_id,
    Category.id_comp, Iso.inv_hom_id]

/-- 概要：共通 Koszul 表示の全非空有限重なりの dg 代数関手。
方針：指定同型による共役遷移と証明済み関手法則を使う。
規約：KST Lemma 3.6、係数変更の具体的公式との一致は別に公開する。
使われ方：例外因子の共通表示との図式比較。 -/
def finiteOverlapExceptionalProductDiagram (a : I → R) :
    FiniteOverlapIndex I ⥤ Mon (Complex R) where
  obj T := finiteOverlapExceptionalProductAlgebra R a (finiteOverlapIndexPivot T) T.val
  map {T U} f := finiteOverlapExceptionalProductMap R a
    (finiteOverlapIndexPivot T) (finiteOverlapIndexPivot U)
    (leOfHom f) (finiteOverlapIndexPivot_mem T)
  map_id T := finiteOverlapExceptionalProductMap_id R a _ T.val (finiteOverlapIndexPivot_mem T)
  map_comp {T U _V} f g := (finiteOverlapExceptionalProductMap_comp R a _ _ _
    (leOfHom f) (leOfHom g) (finiteOverlapIndexPivot_mem T) (finiteOverlapIndexPivot_mem U)).symm

/-- 概要：例外因子の元の係数図式と共通 Koszul 表示の指定自然同型。
方針：各頂点に指定 dg 代数同型を取り、共役の定義から自然性を示す。
規約：KST Lemma 3.6、層の降下や Perf の模型同値とは区別する。
使われ方：E∩U_i の Ko(A;a)[S] 表示を全重なりで同時に使用する。 -/
def finiteOverlapExceptionalProductDiagramIso (a : I → R) :
    finiteOverlapExceptionalDGAlgebraDiagram R a ≅ finiteOverlapExceptionalProductDiagram R a :=
  NatIso.ofComponents
    (fun T => finiteOverlapExceptionalProductIso R a (finiteOverlapIndexPivot T) T.val)
    (by
      intro T U f
      change finiteOverlapExceptionalDGAlgebraMap R a _ _ _ _ ≫
          (finiteOverlapExceptionalProductIso R a _ _).hom =
        (finiteOverlapExceptionalProductIso R a _ _).hom ≫
          finiteOverlapExceptionalProductMap R a _ _ _ _
      simp only [finiteOverlapExceptionalProductMap, Iso.hom_inv_id_assoc])

end SerrePositivity.KST.DerivedBlowup
