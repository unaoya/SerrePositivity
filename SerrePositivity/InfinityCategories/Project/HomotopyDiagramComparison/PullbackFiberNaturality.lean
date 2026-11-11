module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PullbackFiberIso

/-!
概要：引き戻しの fiber の標準同型と可換正方形の自然性。
方針：元の全空間への包含の後で検査し、同型を通して π_* と π₀ の比較を移す。
規約：零次数の全射性を移す補題には Kan 性や非空性を要求しない。
使われ方：Goerss–Jardine I §§7–8、Sp の引き戻しの Ω 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：二つの引き戻しの比較は指定頂点上の fiber の標準同型と可換。
方針：標的の fiber の包含後で、第一射影に関する可換条件を使う。
規約：両方の底の頂点の等式を明示し、空の fiber も扱う。
使われ方：元の fibration の fiber 比較を引き戻しの fiber 比較へ移す。 -/
lemma pullbackFiberIso_naturality
    {P E X B P' E' X' B' : SSet.{u}}
    {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    {i' : P' ⟶ E'} {j' : P' ⟶ X'} {p' : E' ⟶ B'} {q' : X' ⟶ B'}
    (hP : IsPullback i j p q) (hP' : IsPullback i' j' p' q')
    (aP : P ⟶ P') (aE : E ⟶ E') (aX : X ⟶ X') (aB : B ⟶ B')
    (hi : i ≫ aE = aP ≫ i') (hj : j ≫ aX = aP ≫ j')
    (hp : p ≫ aB = aE ≫ p') (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) (hxb' : q'.app _ (aX.app _ x) = aB.app _ b) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase j j' aP aX hj x ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberIso hP' (aX.app _ x) (aB.app _ b) hxb').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberIso hP x b hxb).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' aE aB hp b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p' (aB.app _ b)
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase j j' aP aX hj x ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberToOriginal hP' (aX.app _ x) (aB.app _ b) hxb') ≫ _ =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberToOriginal hP x b hxb ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' aE aB hp b) ≫ _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberToOriginal_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_ι, Category.assoc, ← hi, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberToOriginal_ι hP x b hxb, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_ι p p' aE aB hp b, ← Category.assoc]

/-- 概要：同型による可換な表示の変更は全基点 π_* 同型性を源の射へ戻す。
方針：同型と後の射の合成の π_* 同型性を前後の同型で打ち消す。
規約：四つの単体集合は Kan とする。
使われ方：fiber の標準同型を通した全次数比較。 -/
lemma kanPiIsomorphism_of_iso_square {A B C D : SSet.{u}}
    [KanComplex A] [KanComplex B] [KanComplex C] [KanComplex D]
    (e : A ≅ B) (e' : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ e'.hom = e.hom ≫ g) (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  have hs : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e
  have ht : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e'.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e'
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := e'.hom) _ ht
  rw [h]
  exact hs.comp hg

/-- 概要：同型による可換な表示の変更は連結成分の全射性を源の射へ戻す。
方針：標的の同型で写して持ち上げ、源の逆同型で戻し、標的の逆同型で等号を確認する。
規約：Kan 性や非空性を仮定せず空の単体集合も扱う。
使われ方：引き戻しの空の fiber を含む零次数比較。 -/
lemma piZero_surjective_of_iso_square {A B C D : SSet.{u}}
    (e : A ≅ B) (e' : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ e'.hom = e.hom ≫ g) (hg : Function.Surjective (mapπ₀ g)) :
    Function.Surjective (mapπ₀ f) := by
  intro c
  obtain ⟨b, hb⟩ := hg (mapπ₀ e'.hom c)
  have he : mapπ₀ e.hom (mapπ₀ e.inv b) = b := by
    rw [← mapπ₀_comp_apply, e.inv_hom_id, mapπ₀_id_apply]
  have hh : mapπ₀ e'.hom (mapπ₀ f (mapπ₀ e.inv b)) = mapπ₀ e'.hom c := by
    rw [← mapπ₀_comp_apply, h, mapπ₀_comp_apply, he, hb]
  refine ⟨mapπ₀ e.inv b, ?_⟩
  have hi := congrArg (mapπ₀ e'.inv) hh
  simpa only [← mapπ₀_comp_apply, Category.assoc, e'.hom_inv_id,
    Category.comp_id, mapπ₀_id_apply] using hi

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
