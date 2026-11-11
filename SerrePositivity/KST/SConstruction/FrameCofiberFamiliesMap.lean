module
public import SerrePositivity.KST.SConstruction.FrameCofiberShapes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexInternalHom

/-! # 零対角の枠の図式の族から cofiber の族への自然な写像
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
規約：零対角条件なしで定義する。使われ方：cofiber 抽出のパラメーター自然性。 -/
def frameCofiberFamilyOperator (n : ℕ) (C : SSet.{u}) :
    (ihom (frameNerve n)).obj C ⟶ (ihom (frameNerve n)).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) :=
  (pre ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (frameNerve n)).hom ≫ frameCofiberSquareMap n)).app C ≫
    (ihomCurryIso (Δ[1] ⊗ Δ[1] : SSet.{u}) (frameNerve n) C).hom

/-- 概要：抽出の作用素の頂点は各図式から取った自然な cofiber 四角形の族。
方針：内部 currying を零次元で計算する。
規約：厳密等号。使われ方：零対角条件の頂点での確認。 -/
lemma frameCofiberFamilyOperator_vertex {n : ℕ} {C : SSet.{u}} (F : frameNerve n ⟶ C) :
    (frameCofiberFamilyOperator n C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (frameCofiberFamily F) := rfl

/-- 概要：零対角の枠の図式の抽出した族の各頂点は cofiber 四角形。
方針：充満部分複体に持ち上げた族の零単体条件を使う。
規約：C は quasicategory。使われ方：内部 Hom の全部分複体への持ち上げ。 -/
lemma IsZeroFrameVertex.frameCofiberFamily_vertex {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] {F : frameNerve n ⟶ C}
    (hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (a : (frameNerve n) _⦋0⦌) :
    IsCofiberDiagramVertex ((frameCofiberFamily F).app (Opposite.op ⦋0⦌) a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((zeroFrameCofiberFamily F hF).app (Opposite.op ⦋0⦌) a)

/-- 概要：全 零対角の枠の図式の族から 枠 上の cofiber 図式の族を取る。
方針：各頂点で cofiber 条件を確認し、内部 Hom の全部分複体表示を逆向きに使う。
規約：全てのパラメーターに厳密に自然。使われ方：第一行復元の相対境界データ。 -/
def zeroFrameCofiberFamiliesMap (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    zeroFrameDiagrams n C ⟶ (ihom (frameNerve n)).obj (cofiberDiagrams C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies (frameNerve n)
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) IsCofiberDiagramVertex)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι ≫ frameCofiberFamilyOperator n C) (by
      intro v
      let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (frameNerve n) C).symm v.val
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply v.val
      have hF : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
        rw [hv]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies _ _ _
        ((frameCofiberFamilyOperator n C).app (Opposite.op ⦋0⦌) v.val)
      rw [← hv, frameCofiberFamilyOperator_vertex]
      intro a
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
      exact hF.frameCofiberFamily_vertex a) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso (frameNerve n)
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) IsCofiberDiagramVertex).inv

/-- 概要：族の cofiber 条件を忘れると元の自然な四角形の抽出に一致する。
方針：内部 Hom の全部分複体同型と持ち上げの包含後の式を使う。
規約：厳密等号。使われ方：cofiber 補完の境界を元の 零対角の枠の図式と照合する。 -/
lemma zeroFrameCofiberFamiliesMap_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    zeroFrameCofiberFamiliesMap n C ≫
      (ihom (frameNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι ≫ frameCofiberFamilyOperator n C := by
  rw [zeroFrameCofiberFamiliesMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso_inv_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]

/-- 概要：cofiber 抽出の作用素を右上角で評価すると恒等作用素。
方針：内部 Hom の各成分を計算し、添字の右上角の恒等式を用いる。
規約：全次数で厳密な等号。使われ方：任意のパラメーター付き境界の回収。 -/
lemma frameCofiberFamilyOperator_apex (n : ℕ) (C : SSet.{u}) :
    frameCofiberFamilyOperator n C ≫ (ihom (frameNerve n)).map
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
  change F.app e (α ≫ 𝟙 e) ((frameCofiberSquareMap n).app e
    ((frameNerve n).map (𝟙 e) a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
      stdSimplex.obj₀Equiv.symm (1 : Fin 2)) e.unop.len)) = F.app e α a
  rw [Category.comp_id, CategoryTheory.Functor.map_id_apply]
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app (frameCofiberSquareMap_apex n) e) a
  change (frameCofiberSquareMap n).app e
    (a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
      stdSimplex.obj₀Equiv.symm (1 : Fin 2)) e.unop.len) = a at he
  rw [he]

/-- 概要：零対角の枠の図式の族を cofiber 族にして右上角を取ると元の族。
方針：全部分複体の包含後の式と内部 Hom の後合成の合成則を使う。
規約：任意の高次パラメーターでも厳密。使われ方：相対補完の境界の保存。 -/
lemma zeroFrameCofiberFamiliesMap_apex (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    zeroFrameCofiberFamiliesMap n C ≫ (ihom (frameNerve n)).map (cofiberApex C) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι := by
  rw [cofiberApex, Functor.map_comp, ← Category.assoc, zeroFrameCofiberFamiliesMap_ι,
    Category.assoc, frameCofiberFamilyOperator_apex]
  exact Category.comp_id _

end SerrePositivity.KST.SConstruction
