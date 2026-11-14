module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects

/-!
概要：元の辺集合に対する S-equivalence とその基本的な閉性を構成する。
方針：局所対象への写像空間の同値で検出し、前合成の合成則を使う。
規約：強飽和性・反射の存在は仮定しない。使われ方：HTT 5.5.4.1・5.5.4.2。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 元の指定辺集合に対する全局所対象への写像空間で検出する S-equivalence。 -/
def LocalEquivalenceHom (W : Set (X _⦋1⦌)) {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) : Prop :=
  ∀ z : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom f z

/-- HTT 5.5.4.1 の S-equivalence を元の一次単体の集合として表す。 -/
def localEquivalences (W : Set (X _⦋1⦌)) : Set (X _⦋1⦌) :=
  {s | LocalEquivalenceHom W (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s))}

/-- 同型は全ての局所対象に対する S-equivalence。 -/
lemma LocalEquivalenceHom.of_isIso (W : Set (X _⦋1⦌)) {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) [IsIso f] :
    LocalEquivalenceHom W f := fun z _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_of_isIso f z

/-- S-equivalence は hX の射の合成で閉じる。 -/
lemma LocalEquivalenceHom.comp {W : Set (X _⦋1⦌)} {x y z : X _⦋0⦌}
    {f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y}
    {g : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z}
    (hf : LocalEquivalenceHom W f) (hg : LocalEquivalenceHom W g) :
    LocalEquivalenceHom W (f ≫ g) := fun t ht ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_comp f g t (hf t ht) (hg t ht)

/-- S-equivalence の左因子と合成から右因子を回収する。 -/
lemma LocalEquivalenceHom.cancel_left {W : Set (X _⦋1⦌)} {x y z : X _⦋0⦌}
    {f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y}
    {g : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z}
    (hf : LocalEquivalenceHom W f) (hfg : LocalEquivalenceHom W (f ≫ g)) :
    LocalEquivalenceHom W g := fun t ht ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_cancel_left f g t (hf t ht) (hfg t ht)

/-- S-equivalence の右因子と合成から左因子を回収する。 -/
lemma LocalEquivalenceHom.cancel_right {W : Set (X _⦋1⦌)} {x y z : X _⦋0⦌}
    {f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y}
    {g : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z}
    (hg : LocalEquivalenceHom W g) (hfg : LocalEquivalenceHom W (f ≫ g)) :
    LocalEquivalenceHom W f := fun t ht ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_cancel_right f g t (hg t ht) (hfg t ht)

/-- 元の辺は、それらの局所対象が検出する S-equivalence に含まれる。 -/
lemma subset_localEquivalences (W : Set (X _⦋1⦌)) : W ⊆ localEquivalences W :=
  fun s hs _ hz ↦ hz s hs

/-- 辺集合の拡大に対して局所対象の条件は反変。 -/
lemma isLocalObject_of_subset {W V : Set (X _⦋1⦌)} (h : W ⊆ V) {z : X _⦋0⦌}
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject V z) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z := fun s hs ↦ hz s (h hs)

/-- S-equivalence の生成は元の辺集合に対して単調。 -/
lemma localEquivalences_mono {W V : Set (X _⦋1⦌)} (h : W ⊆ V) :
    localEquivalences W ⊆ localEquivalences V :=
  fun _ hs z hz ↦ hs z (isLocalObject_of_subset h hz)

/-- S-equivalence への拡大は元の局所対象を変えない。 -/
lemma isLocalObject_localEquivalences_iff (W : Set (X _⦋1⦌)) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (localEquivalences W) z ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z := by
  constructor
  · exact isLocalObject_of_subset (subset_localEquivalences W)
  · intro hz s hs
    exact hs z hz

/-- 局所対象で検出した辺集合の拡大は冪等。強飽和性・小生成性は別に証明する。 -/
lemma localEquivalences_idempotent (W : Set (X _⦋1⦌)) :
    localEquivalences (localEquivalences W) = localEquivalences W := by
  apply Set.Subset.antisymm
  · intro s hs z hz
    exact hs z ((isLocalObject_localEquivalences_iff W z).mpr hz)
  · exact subset_localEquivalences _

end
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.4.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences
