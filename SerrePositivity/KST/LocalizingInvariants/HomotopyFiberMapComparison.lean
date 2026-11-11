module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberMapNaturality
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.GroupFiveLemma
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：元の源と底の整数 π 同型は、構成した homotopy fiber 比較射の整数 π 同型を導く。
方針：元の二辺と接続射に自然な全整数長完全列の五項へ群の五項補題を適用する。
規約：比較射は実 BF 射であり選び直さない。使われ方：fiber 模型の同値による移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyFiberComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

include h in
lemma right_natural (j : ℤ) (x : homotopyGroup X j) :
    homotopyMap b j (homotopyMap p j x) = homotopyMap q j (homotopyMap a j x) := by
  have he := congrArg (fun f => homotopyMap f j) h
  rw [homotopyMap_comp, homotopyMap_comp] at he
  exact DFunLike.congr_fun he x

lemma inclusion_natural (j : ℤ) (x : homotopyGroup (homotopyFiber p) j) :
    homotopyMap a j (homotopyMap (homotopyFiberInclusion p) j x) =
      homotopyMap (homotopyFiberInclusion q) j (homotopyMap (map p q a b h) j x) := by
  have he := congrArg (fun f => homotopyMap f j) (map_inclusion p q a b h)
  rw [homotopyMap_comp, homotopyMap_comp] at he
  exact (DFunLike.congr_fun he x).symm

lemma map_piIsomorphism (ha : PiIsomorphism a) (hb : PiIsomorphism b) :
    PiIsomorphism (map p q a b h) := by
  intro j
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_five_lemma
    (homotopyMap p (j + 1)) (homotopyFiberBoundary p j)
    (homotopyMap (homotopyFiberInclusion p) j) (homotopyMap p j)
    (homotopyMap q (j + 1)) (homotopyFiberBoundary q j)
    (homotopyMap (homotopyFiberInclusion q) j) (homotopyMap q j)
    (homotopyMap a (j + 1)) (homotopyMap b (j + 1)) (homotopyMap (map p q a b h) j)
    (homotopyMap a j) (homotopyMap b j)
    (right_natural p q a b h (j + 1)) (boundary_natural p q a b h j)
    (inclusion_natural p q a b h j) (right_natural p q a b h j)
    (homotopy_exact_total_base p j) (homotopy_exact_connecting_fiber p j)
    (homotopy_exact_fiber_total p j) (homotopy_exact_total_base q j)
    (homotopy_exact_connecting_fiber q j) (homotopy_exact_fiber_total q j)
    (ha (j + 1)) (hb (j + 1)) (ha j) (hb j)

local instance comparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

lemma map_isInvertible (ha : PiIsomorphism a) (hb : PiIsomorphism b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (map p q a b h)).toTruncated :=
  isInvertible_of_piIsomorphism _ (map_piIsomorphism p q a b h ha hb)

end SerrePositivity.KST.LocalizingInvariants.HomotopyFiberComparison
