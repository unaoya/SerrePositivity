module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
概要：非空の余積の脚から生成した篩に、脚と初対象を含む指定添字を組む。
方針：既存の Discrete と WithTerminal.lift を使い、全三角形を同じ初対象の射で作る。
規約：HTT 6.2.2.6 の extensive 位相での入力。一般の射の一本の脚への分解は仮定しない。
使われ方：S1 の有限積による層条件の判定。空族は別の枝で扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {ι : Type u} {B : ι → C}

/-- 元の cofan の同じ脚が生成する篩。 -/
abbrev cofanGeneratedSieve (c : Cofan B) : Sieve c.pt := Sieve.ofArrows B c.inj

/-- 各脚そのものは、元の生成篩の対象。 -/
def cofanSieveLeg (c : Cofan B) (i : ι) : sieveCategory (cofanGeneratedSieve c) :=
  ⟨Over.mk (c.inj i), Sieve.ofArrows_mk B c.inj i⟩

/-- 非空族の場合、初対象からの射も同じ篩に属する。 -/
def cofanSieveInitial [HasInitial C] [Nonempty ι] (c : Cofan B) :
    sieveCategory (cofanGeneratedSieve c) :=
  ⟨Over.mk (initial.to c.pt), by
    let i : ι := Classical.choice inferInstance
    change (cofanGeneratedSieve c) (initial.to c.pt)
    have h := (cofanGeneratedSieve c).downward_closed (cofanSieveLeg c i).property
      (initial.to (B i))
    change (cofanGeneratedSieve c) (initial.to (B i) ≫ c.inj i) at h
    simpa only [initial.to_comp] using h⟩

/-- 同じ初対象の射は、篩の中で各脚への射を与える。 -/
def cofanSieveInitialToLeg [HasInitial C] [Nonempty ι] (c : Cofan B) (i : ι) :
    cofanSieveInitial c ⟶ cofanSieveLeg c i :=
  ObjectProperty.homMk (Over.homMk (initial.to (B i)) (by
    apply initialIsInitial.hom_ext))

/-- 脚と初対象を同時に保持する、元の篩の反対への全添字関手。 -/
def cofanSieveIndex [HasInitial C] [Nonempty ι] (c : Cofan B) :
    WithTerminal (Discrete ι) ⥤ (sieveCategory (cofanGeneratedSieve c))ᵒᵖ :=
  WithTerminal.lift (Discrete.functor (fun i => Opposite.op (cofanSieveLeg c i)))
    (fun i => (cofanSieveInitialToLeg c i.as).op) (by
      rintro ⟨i⟩ ⟨j⟩ f
      obtain rfl := Discrete.eq_of_hom f
      have hf : f = 𝟙 (Discrete.mk i) := Subsingleton.elim _ _
      subst f
      rw [CategoryTheory.Functor.map_id, Category.id_comp])

/-- 分解を使うのは、生成篩の対象そのものに限る。 -/
lemma cofanSieveFactorization (c : Cofan B) (s : sieveCategory (cofanGeneratedSieve c)) :
    ∃ (i : ι) (f : s.obj.left ⟶ B i), s.obj.hom = f ≫ c.inj i :=
  (Sieve.mem_ofArrows_iff B c.inj s.obj.hom).mp s.property

/-- 初対象でない始域の分解の脚は、有限余積の非交叉性により一意。 -/
lemma cofanFactorization_label_unique [FinitaryExtensive C] [Finite ι]
    (c : Cofan B) (hc : IsColimit c) {V : C} (hV : ¬ Nonempty (IsInitial V))
    {i j : ι} (f : V ⟶ B i) (g : V ⟶ B j)
    (h : f ≫ c.inj i = g ≫ c.inj j) : i = j := by
  by_contra hij
  have hp := FinitaryExtensive.isPullback_initial_to hc (Discrete.mk i) (Discrete.mk j)
    (fun e => hij (congrArg Discrete.as e))
  exact hV ⟨IsInitial.ofStrict (hp.isLimit.lift (PullbackCone.mk f g h)) initialIsInitial⟩

/-- 同じ脚への二つの分解の射は、その脚の単射性で一意。 -/
lemma cofanFactorization_arrow_unique [FinitaryExtensive C] [Finite ι]
    (c : Cofan B) (hc : IsColimit c) {V : C} (i : ι) (f g : V ⟶ B i)
    (h : f ≫ c.inj i = g ≫ c.inj i) : f = g := by
  letI : Mono (c.inj i) := FinitaryExtensive.mono_ι hc (Discrete.mk i)
  exact (cancel_mono (c.inj i)).mp h

end SerrePositivity.InfinityCategories.Sheaves
