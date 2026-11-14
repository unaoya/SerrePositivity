module

public import SerrePositivity.EInfinity.Interface.PrimeField

/-!
# 持ち上げた素体からの係数の制限

BS 著者版 Lemma 8.4 に使う May の P⁰ の補助。
本欄を F_p に限り、一般の標数 p の係数環ではこの構造射で制限して読む。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity

/-- 界面の素体から任意の標数 p の係数環への標準構造射。 -/
def eInfinityPrimeFieldMap (p : ℕ) (k : Type u) [CommRing k] [CharP k p] :
    EInfinityPrimeField.{u} p →+* k :=
  (ZMod.castHom (dvd_refl p) k).comp (eInfinityPrimeFieldEquiv p).toRingHom

end SerrePositivity.EInfinity
