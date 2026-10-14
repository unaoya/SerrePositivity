module

public import SerrePositivity.PerfectComplex.TensorShortExact
public import SerrePositivity.PerfectComplex.TensorTriple

/-! # Degreewise split short exact sequences in each of three tensor positions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

abbrev cochainTensorTripleShortComplexFirst
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (Q T : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorShortComplexRight (cochainTensorShortComplexRight S Q) T

abbrev cochainTensorTripleShortComplexSecond
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (T : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorShortComplexRight (cochainTensorShortComplexLeft P S) T

abbrev cochainTensorTripleShortComplexThird
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :=
  cochainTensorShortComplexLeft (cochainTensor P Q) S

lemma cochainTensorTripleShortComplexFirst_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorTripleShortComplexFirst S Q T).ShortExact :=
  cochainTensorShortComplexRight_shortExact (cochainTensorShortComplexRight S Q)
    (cochainTensorShortComplexRightSplitting S σ Q) T

lemma cochainTensorTripleShortComplexSecond_shortExact
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorTripleShortComplexSecond P S T).ShortExact :=
  cochainTensorShortComplexRight_shortExact (cochainTensorShortComplexLeft P S)
    (cochainTensorShortComplexLeftSplitting P S σ) T

lemma cochainTensorTripleShortComplexThird_shortExact
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) :
    (cochainTensorTripleShortComplexThird P Q S).ShortExact :=
  cochainTensorShortComplexLeft_shortExact (cochainTensor P Q) S σ

end SerrePositivity
