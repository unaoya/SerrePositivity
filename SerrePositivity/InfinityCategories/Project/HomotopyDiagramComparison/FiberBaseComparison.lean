module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PullbackFiberNaturality

/-!
概要：fiber の底の頂点の表示の変更と全空間の比較。
方針：底の等式による同型と包含の普遍性で二つの fiber 射の表示を同定する。
規約：空の fiber の成分の全射性は別の前提として保持する。
使われ方：Goerss–Jardine I §§7–8、Sp の引き戻しの Ω 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.FibrationSquare
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：等しい底の頂点上の fiber を同型で移す。
方針：頂点の等式による対象の等号を同型にする。
規約：Kan 性は不要。
使われ方：fiber 射の二つの標的の表示を合わせる。 -/
def fiberBaseIso {E B : SSet.{u}} (p : E ⟶ B) (b b' : B _⦋0⦌) (h : b = b') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b' := eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p) h)

/-- 概要：底の等号による fiber の同型は包含を変えない。
方針：等式で帰納して恒等同型を計算する。
規約：射として厳密に一致する。
使われ方：fiber の標的の移送の一意性。 -/
lemma fiberBaseIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b b' : B _⦋0⦌) (h : b = b') :
    (fiberBaseIso p b b' h).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b' = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b := by
  subst b'
  simp [fiberBaseIso]

/-- 概要：任意の底で定義した fiber 射を頂点の像で移すと既存の fiberMap に一致する。
方針：標的の包含の後で二つの射を比較する。
規約：移送には元の可換正方形が与える底の等号を使う。
使われ方：任意の底上の比較を L9 の長完全列の標準の fiberMap に渡す。 -/
lemma fibrationFiberMapBase_to_fiberMap {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm (p.app _ e) ≫
        (fiberBaseIso p' _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e)).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p' (p'.app _ (f.app _ e))
  rw [Category.assoc, fiberBaseIso_hom_ι, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι]

/-- 概要：任意の底上の fiber 射の条件から全空間の全基点 π_* 同型性を得る。
方針：標的の表示を移して既存の全空間比較へ渡す。
規約：全 fiber の成分の全射性を全基点条件とは別に要求する。
使われ方：引き戻しの fiber の同型を使った全空間比較。 -/
lemma fibrationTotal_piIsomorphism_of_base {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g)
    (hF : ∀ b, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b))
    (hF₀ : ∀ b, Function.Surjective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationTotal_piIsomorphism p p' f g comm hg _ hF₀
  intro e
  have hi : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (fiberBaseIso p' _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e)).hom :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso _
  have h := (hF (p.app _ e)).comp hi
  rw [fibrationFiberMapBase_to_fiberMap] at h
  exact h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
