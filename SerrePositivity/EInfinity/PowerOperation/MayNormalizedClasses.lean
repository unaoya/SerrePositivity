module

public import SerrePositivity.EInfinity.PowerOperation.MayBaseFieldDClassAdditivity
public import SerrePositivity.EInfinity.PowerOperation.MayPowerZeroCycles

/-!
# 指定した規格化係数で読む May のホモロジー演算

May, Definition 2.2・Proposition 2.3。宇宙を持ち上げた F_p の場合にも、
同じ D_i と指定係数 ν の像を用いて演算を読むための補助。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.DifferentialGraded
variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (X : (operad k).Algebra) (n : ℤ) (c : k)

lemma mayHomologyIndex_naturality {K L : Complex k} (f : K ⟶ L)
    {i j : ℤ} (h : i = j) (a : K.homology i) :
    homologyMap f j ((eqToHom (congrArg (fun t : ℤ => K.homology t) h)).hom a) =
      (eqToHom (congrArg (fun t : ℤ => L.homology t) h)).hom (homologyMap f i a) := by
  subst j
  rfl

/-- 同じ指定 D_i を、指定された係数で規格化して H^{-n} へ送る。 -/
def mayNormalizedClass (a : MayClosed X.carrier (-n)) : X.carrier.homology (-n) :=
  if hn : 0 ≤ mayZeroIndex p n then
    c • (eqToHom (congrArg (fun i : ℤ => X.carrier.homology i)
      (mayPowerZero_degree p n hn))).hom
        (mayDClass p X (mayZeroIndex p n).toNat (-n) a)
  else 0

lemma mayNormalizedClass_independent (a b : MayClosed X.carrier (-n))
    (hab : mayClosedClass X.carrier (-n) a = mayClosedClass X.carrier (-n) b) :
    mayNormalizedClass p X n c a = mayNormalizedClass p X n c b := by
  unfold mayNormalizedClass
  split_ifs with hn
  · rw [mayDClass_independent p X _ _ a b hab]
  · rfl

lemma mayNormalizedClass_add (a b : MayClosed X.carrier (-n)) :
    mayNormalizedClass p X n c (a + b) =
      mayNormalizedClass p X n c a + mayNormalizedClass p X n c b := by
  unfold mayNormalizedClass
  split_ifs with hn
  · rw [mayBaseFieldDClass_add, map_add, smul_add]
  · exact (zero_add _).symm

lemma mayNormalizedClass_naturality {Y : (operad k).Algebra} (f : X ⟶ Y)
    (a : MayClosed X.carrier (-n)) :
    homologyMap f.hom (-n) (mayNormalizedClass p X n c a) =
      mayNormalizedClass p Y n c (mayClosedMap f.hom (-n) a) := by
  unfold mayNormalizedClass
  split_ifs with hn
  · rw [map_smul, mayHomologyIndex_naturality f.hom (mayPowerZero_degree p n hn),
      mayDClass_naturality]
  · exact map_zero _

/-- 同じ指定演算を代表元に依存しない実ホモロジーの関数へ降ろす。 -/
def mayNormalizedHomology (x : X.carrier.homology (-n)) : X.carrier.homology (-n) :=
  mayNormalizedClass p X n c (mayClosedRepresentative X.carrier (-n) x)

lemma mayNormalizedHomology_class (a : MayClosed X.carrier (-n)) :
    mayNormalizedHomology p X n c (mayClosedClass X.carrier (-n) a) =
      mayNormalizedClass p X n c a := by
  apply mayNormalizedClass_independent
  exact mayClosedRepresentative_spec X.carrier (-n) _

lemma mayNormalizedHomology_add (x y : X.carrier.homology (-n)) :
    mayNormalizedHomology p X n c (x + y) =
      mayNormalizedHomology p X n c x + mayNormalizedHomology p X n c y := by
  obtain ⟨a, rfl⟩ := mayClosedClass_surjective X.carrier (-n) x
  obtain ⟨b, rfl⟩ := mayClosedClass_surjective X.carrier (-n) y
  rw [← map_add, mayNormalizedHomology_class, mayNormalizedHomology_class,
    mayNormalizedHomology_class, mayNormalizedClass_add]

def mayNormalizedAddHom : X.carrier.homology (-n) →+ X.carrier.homology (-n) :=
  AddMonoidHom.mk' (mayNormalizedHomology p X n c) (mayNormalizedHomology_add p X n c)

lemma mayNormalizedHomology_naturality {Y : (operad k).Algebra} (f : X ⟶ Y)
    (x : X.carrier.homology (-n)) :
    homologyMap f.hom (-n) (mayNormalizedHomology p X n c x) =
      mayNormalizedHomology p Y n c (homologyMap f.hom (-n) x) := by
  let a := mayClosedRepresentative X.carrier (-n) x
  have ha : mayClosedClass X.carrier (-n) a = x := mayClosedRepresentative_spec X.carrier (-n) x
  rw [← ha, mayNormalizedHomology_class, mayNormalizedClass_naturality,
    mayClosedClass_naturality, mayNormalizedHomology_class]

end SerrePositivity.EInfinity.PowerOperation
