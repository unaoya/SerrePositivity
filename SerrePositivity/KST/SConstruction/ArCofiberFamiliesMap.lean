module
public import SerrePositivity.KST.SConstruction.ArCofiberFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexInternalHom

/-! # gapped 図式の族から cofiber の族への自然な写像
概要：cofiber 四角形の抽出を全てのパラメーターで同時に行う。
方針：内部 currying と全部分複体を標的とする内部 Hom の表示を使う。
規約：図式の頂点ごとに別々に選択しない。使われ方：既存境界の相対 cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：cofiber 四角形の抽出を関手単体集合の射として構成する。
方針：自然な添字写像による前合成と内部 currying を合成する。
規約：gapped 条件なしで定義する。使われ方：cofiber 抽出のパラメーター自然性。 -/
def arCofiberFamilyOperator (n : ℕ) (C : SSet.{u}) :
    (ihom (arNerve n)).obj C ⟶ (ihom (arNerve n)).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) :=
  (pre ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom ≫ arCofiberSquareMap n)).app C ≫
    (ihomCurryIso (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C).hom

/-- 概要：抽出の作用素の頂点は各図式から取った自然な cofiber 四角形の族。
方針：内部 currying を零次元で計算する。
規約：厳密等号。使われ方：gapped 条件の頂点での確認。 -/
lemma arCofiberFamilyOperator_vertex {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C) :
    (arCofiberFamilyOperator n C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arCofiberFamily F) := rfl

/-- 概要：gapped 図式の抽出した族の各頂点は cofiber 四角形。
方針：充満部分複体に持ち上げた族の零単体条件を使う。
規約：quasicategory 性は不要。使われ方：内部 Hom の全部分複体への持ち上げ。 -/
lemma IsGapped.arCofiberFamily_vertex {n : ℕ} {C : SSet.{u}} {F : arNerve n ⟶ C}
    (hF : IsGapped F) (a : (arNerve n) _⦋0⦌) :
    IsCofiberDiagramVertex ((arCofiberFamily F).app (Opposite.op ⦋0⦌) a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((gappedCofiberFamily hF).app (Opposite.op ⦋0⦌) a)

/-- 概要：全 gapped 図式の族から Ar[n] 上の cofiber 図式の族を取る。
方針：各頂点で cofiber 条件を確認し、内部 Hom の全部分複体表示を逆向きに使う。
規約：全てのパラメーターに厳密に自然。使われ方：第一行復元の相対境界データ。 -/
def gappedCofiberFamiliesMap (n : ℕ) (C : SSet.{u}) :
    sConstruction n C ⟶ (ihom (arNerve n)).obj (cofiberDiagrams C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (arNerve n)
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) IsCofiberDiagramVertex)
    ((gappedSubcomplex n C).ι ≫ arCofiberFamilyOperator n C) (by
      intro v
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply v.val
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies _ _ _
        ((arCofiberFamilyOperator n C).app (Opposite.op ⦋0⦌) v.val)
      rw [← hv, arCofiberFamilyOperator_vertex]
      intro a
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
      exact (gappedDiagram_isGapped v).arCofiberFamily_vertex a) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso (arNerve n)
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) IsCofiberDiagramVertex).inv

/-- 概要：族の cofiber 条件を忘れると元の自然な四角形の抽出に一致する。
方針：内部 Hom の全部分複体同型と持ち上げの包含後の式を使う。
規約：厳密等号。使われ方：cofiber 補完の境界を元の gapped 図式と照合する。 -/
lemma gappedCofiberFamiliesMap_ι (n : ℕ) (C : SSet.{u}) :
    gappedCofiberFamiliesMap n C ≫
      (ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      (gappedSubcomplex n C).ι ≫ arCofiberFamilyOperator n C := by
  rw [gappedCofiberFamiliesMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso_inv_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]

/-- 概要：cofiber 抽出の作用素を右上角で評価すると恒等作用素。
方針：内部 Hom の各成分を計算し、添字の右上角の恒等式を用いる。
規約：全次数で厳密な等号。使われ方：任意のパラメーター付き境界の回収。 -/
lemma arCofiberFamilyOperator_apex (n : ℕ) (C : SSet.{u}) :
    arCofiberFamilyOperator n C ≫ (ihom (arNerve n)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro a
  change F.app e (α ≫ 𝟙 e) ((arCofiberSquareMap n).app e
    ((arNerve n).map (𝟙 e) a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
      stdSimplex.obj₀Equiv.symm (1 : Fin 2)) e.unop.len)) = F.app e α a
  rw [Category.comp_id, CategoryTheory.Functor.map_id_apply]
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app (arCofiberSquareMap_apex n) e) a
  change (arCofiberSquareMap n).app e
    (a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
      stdSimplex.obj₀Equiv.symm (1 : Fin 2)) e.unop.len) = a at he
  rw [he]

/-- 概要：gapped 図式の族を cofiber 族にして右上角を取ると元の族。
方針：全部分複体の包含後の式と内部 Hom の後合成の合成則を使う。
規約：任意の高次パラメーターでも厳密。使われ方：相対補完の境界の保存。 -/
lemma gappedCofiberFamiliesMap_apex (n : ℕ) (C : SSet.{u}) :
    gappedCofiberFamiliesMap n C ≫ (ihom (arNerve n)).map (cofiberApex C) =
      (gappedSubcomplex n C).ι := by
  rw [cofiberApex, Functor.map_comp, ← Category.assoc, gappedCofiberFamiliesMap_ι,
    Category.assoc, arCofiberFamilyOperator_apex]
  exact Category.comp_id _

end SerrePositivity.KST.SConstruction
