module

public import SerrePositivity.InfinityCategories.F1.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberSplitRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomInitiality
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanLimits
public import SerrePositivity.InfinityCategories.Core.JoinCoproductPushout
public import Mathlib.CategoryTheory.Yoneda

/-!
# 二枝の余錐空間の積分解

## 概要
HA 3.2.4.7 の native な二項余積の検査に使う、二枝の終点固定の余錐空間の同型。

## 方針
join の pushout の普遍性で族を貼り、任意のパラメータからの射で同型を検査する。

## 規約
脚と終点を厳密に固定する。余極限の存在や安定性は仮定しない。

## 使われ方
二点図式の余錐空間を二つの左写像空間の積へ比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 固定終点の余錐の族を join からの射へ展開する。 -/
def coconeFamilyUncurry {K X T : SSet.{u}} {p : K ⟶ X} {y : X _⦋0⦌}
    (f : T ⟶ coconeMappingSpace p y) : join K T ⟶ X :=
  sliceUnderUncurry (f ≫ vertexFiberι (sliceUnderProjection p) y)

/-- 余錐の族の左制限は指定された図式。 -/
lemma coconeFamilyUncurry_inl {K X T : SSet.{u}} {p : K ⟶ X} {y : X _⦋0⦌}
    (f : T ⟶ coconeMappingSpace p y) : joinInl K T ≫ coconeFamilyUncurry f = p :=
  sliceUnderUncurry_fixed _

/-- 余錐の族の右制限は指定した終点に定値。 -/
lemma coconeFamilyUncurry_inr {K X T : SSet.{u}} {p : K ⟶ X} {y : X _⦋0⦌}
    (f : T ⟶ coconeMappingSpace p y) : joinInr K T ≫ coconeFamilyUncurry f = SSet.const y := by
  rw [coconeFamilyUncurry, sliceUnderUncurry_projection, Category.assoc,
    vertexFiberι_comp, SSet.comp_const]

/-- 両端の条件を満たす join の射を固定終点の余錐の族へ戻す。 -/
def coconeFamilyCurry {K X T : SSet.{u}} {p : K ⟶ X} {y : X _⦋0⦌}
    (F : join K T ⟶ X) (hp : joinInl K T ≫ F = p)
    (hy : joinInr K T ≫ F = SSet.const y) : T ⟶ coconeMappingSpace p y :=
  vertexFiberLift _ y (sliceUnderCurry F hp) ((sliceUnderCurry_projection F hp).trans hy)

/-- 余錐の族に戻した join の射を展開すると元の射。 -/
lemma coconeFamilyUncurry_curry {K X T : SSet.{u}} {p : K ⟶ X} {y : X _⦋0⦌}
    (F : join K T ⟶ X) (hp : joinInl K T ≫ F = p)
    (hy : joinInr K T ≫ F = SSet.const y) :
    coconeFamilyUncurry (coconeFamilyCurry F hp hy) = F := by
  unfold coconeFamilyUncurry coconeFamilyCurry
  rw [vertexFiberLift_ι, sliceUnderUncurry_curry]

/-- 余錐の族は展開した join の射で決まる。 -/
lemma coconeFamilyUncurry_injective {K X T : SSet.{u}} (p : K ⟶ X) (y : X _⦋0⦌) :
    Function.Injective (coconeFamilyUncurry (T := T) (p := p) (y := y)) := by
  intro f g h
  apply vertexFiber_hom_ext (sliceUnderProjection p) y
  exact sliceUnderUncurry_injective p h

/-- 図式の制限は、族の展開後の join の左因子の制限である。 -/
lemma coconeFamilyUncurry_restrict {K L X T : SSet.{u}} (p : K ⟶ X) (i : L ⟶ K)
    (y : X _⦋0⦌) (f : T ⟶ coconeMappingSpace p y) :
    coconeFamilyUncurry (f ≫ cosliceRestrictionFiberMap p i y) =
      joinMap i (𝟙 T) ≫ coconeFamilyUncurry f := cosliceRestrictionFiberMap_uncurry p i y f

variable {K L X T : SSet.{u}} (p : K ⨿ L ⟶ X) (y : X _⦋0⦌)

/-- 二つの枝への制限を組にした、終点固定の余錐空間の射。 -/
def binaryCoconeSpaceRestriction : coconeMappingSpace p y ⟶
    coconeMappingSpace (coprod.inl ≫ p) y ⨯ coconeMappingSpace (coprod.inr ≫ p) y :=
  prod.lift (cosliceRestrictionFiberMap p coprod.inl y) (cosliceRestrictionFiberMap p coprod.inr y)

/-- 二枝の制限の上で一致する余錐の族は一致する。 -/
lemma binaryCoconeSpace_hom_ext {f g : T ⟶ coconeMappingSpace p y}
    (hl : f ≫ cosliceRestrictionFiberMap p coprod.inl y =
      g ≫ cosliceRestrictionFiberMap p coprod.inl y)
    (hr : f ≫ cosliceRestrictionFiberMap p coprod.inr y =
      g ≫ cosliceRestrictionFiberMap p coprod.inr y) : f = g := by
  apply coconeFamilyUncurry_injective p y
  apply (join_coproduct_isPushout K L T).hom_ext
  · rw [← coconeFamilyUncurry_restrict, ← coconeFamilyUncurry_restrict, hl]
  · rw [← coconeFamilyUncurry_restrict, ← coconeFamilyUncurry_restrict, hr]

/-- 二つの枝の余錐の族を、同じ固定終点で貼った族へまとめる。 -/
def binaryCoconeSpaceGlue
    (f : T ⟶ coconeMappingSpace (coprod.inl ≫ p) y)
    (g : T ⟶ coconeMappingSpace (coprod.inr ≫ p) y) : T ⟶ coconeMappingSpace p y := by
  let P := join_coproduct_isPushout K L T
  let F := coconeFamilyUncurry f
  let G := coconeFamilyUncurry g
  have hc : joinInr K T ≫ F = joinInr L T ≫ G :=
    (coconeFamilyUncurry_inr f).trans (coconeFamilyUncurry_inr g).symm
  let V := P.desc F G hc
  have hp : joinInl (K ⨿ L) T ≫ V = p := by
    apply coprod.hom_ext
    · rw [← Category.assoc, ← joinInl_joinMap (coprod.inl : K ⟶ K ⨿ L) (𝟙 T), Category.assoc,
        P.inl_desc, coconeFamilyUncurry_inl]
    · rw [← Category.assoc, ← joinInl_joinMap (coprod.inr : L ⟶ K ⨿ L) (𝟙 T), Category.assoc,
        P.inr_desc, coconeFamilyUncurry_inl]
  have hy : joinInr (K ⨿ L) T ≫ V = SSet.const y := by
    have h := congrArg (fun q => joinInr K T ≫ q) (P.inl_desc F G hc)
    simpa only [← Category.assoc, joinInr_joinMap, Category.id_comp] using
      h.trans (coconeFamilyUncurry_inr f)
  exact coconeFamilyCurry V hp hy

/-- 貼った族の第一枝は元の第一の族。 -/
lemma binaryCoconeSpaceGlue_left
    (f : T ⟶ coconeMappingSpace (coprod.inl ≫ p) y)
    (g : T ⟶ coconeMappingSpace (coprod.inr ≫ p) y) :
    binaryCoconeSpaceGlue p y f g ≫ cosliceRestrictionFiberMap p coprod.inl y = f := by
  apply coconeFamilyUncurry_injective.{u} (coprod.inl ≫ p) y
  rw [coconeFamilyUncurry_restrict]
  unfold binaryCoconeSpaceGlue
  rw [coconeFamilyUncurry_curry]
  exact (join_coproduct_isPushout K L T).inl_desc _ _ _

/-- 貼った族の第二枝は元の第二の族。 -/
lemma binaryCoconeSpaceGlue_right
    (f : T ⟶ coconeMappingSpace (coprod.inl ≫ p) y)
    (g : T ⟶ coconeMappingSpace (coprod.inr ≫ p) y) :
    binaryCoconeSpaceGlue p y f g ≫ cosliceRestrictionFiberMap p coprod.inr y = g := by
  apply coconeFamilyUncurry_injective.{u} (coprod.inr ≫ p) y
  rw [coconeFamilyUncurry_restrict]
  unfold binaryCoconeSpaceGlue
  rw [coconeFamilyUncurry_curry]
  exact (join_coproduct_isPushout K L T).inr_desc _ _ _

/-- 二枝への制限は、任意のパラメータからの族の上で全単射。 -/
instance binaryCoconeSpaceRestriction_isIso : IsIso (binaryCoconeSpaceRestriction p y) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  constructor
  · intro f g h
    apply binaryCoconeSpace_hom_ext p y
    · simpa only [binaryCoconeSpaceRestriction, Category.assoc, prod.lift_fst] using
        congrArg (fun k => k ≫ prod.fst) h
    · simpa only [binaryCoconeSpaceRestriction, Category.assoc, prod.lift_snd] using
        congrArg (fun k => k ≫ prod.snd) h
  · intro h
    refine ⟨binaryCoconeSpaceGlue p y (h ≫ prod.fst) (h ≫ prod.snd), ?_⟩
    apply prod.hom_ext
    · simp only [binaryCoconeSpaceRestriction, Category.assoc, prod.lift_fst,
        binaryCoconeSpaceGlue_left]
    · simp only [binaryCoconeSpaceRestriction, Category.assoc, prod.lift_snd,
        binaryCoconeSpaceGlue_right]

/-- 二枝の終点固定の余錐空間と、二つの枝の余錐空間の積の指定同型。 -/
def binaryCoconeSpaceIso : coconeMappingSpace p y ≅
    coconeMappingSpace (coprod.inl ≫ p) y ⨯ coconeMappingSpace (coprod.inr ≫ p) y :=
  asIso (binaryCoconeSpaceRestriction p y)

/-- 二枝の余錐空間の積の Kan 性を、指定した積分解から得る。 -/
instance binaryCoconeSpaceProduct_kanComplex [Quasicategory X] :
    KanComplex (coconeMappingSpace ((coprod.inl : K ⟶ K ⨿ L) ≫ p) y ⨯
      coconeMappingSpace ((coprod.inr : L ⟶ K ⨿ L) ≫ p) y) := by
  have : KanComplex (coconeMappingSpace p y) := coconeMappingSpace_kanComplex p y
  exact HomotopyLimits.kanComplex_of_iso (binaryCoconeSpaceIso p y)

/-- HA 3.2.4.7 の二項余積の検査を、指定した全 Hom の族の積比較へ還元する。
ここで比較の同値性は仮定であり、この補題だけでは余極限性を供給しない。 -/
lemma binaryCocone_isColimit_of_pointHomRestriction [Quasicategory X]
    (d : JoinCocone p)
    (h : ∀ z, IsQCatEquivalence
      (HomotopyLimits.coconePointHomFamily d z ≫ binaryCoconeSpaceRestriction p z)) :
    IsColimitCone d := by
  apply (HomotopyLimits.isColimitCone_iff_coconePointHomFamily_homotopyEquivalence d).mpr
  intro z
  have : KanComplex (coconeMappingSpace p z) := coconeMappingSpace_kanComplex p z
  exact ((qCatEquivalenceOfIso (binaryCoconeSpaceIso p z)).isQCatEquivalence.cancel_right
    (h z)).isSimplicialHomotopyEquivalence

end SerrePositivity.EInfinity
