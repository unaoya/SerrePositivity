module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.InitialBridge
public import SerrePositivity.BhattScholze.PerfectoidizationInterface.ExcisionBridge

/-! # 四つの指定普遍環からの excision

概要：界面と四つの IsPerfectoidization から、環の引き戻しと差の全射性を得る。
方針：指定錐を始対象で計算した離散性を、Disc 仮定付きの橋へ合成する。
規約：旧文献入力には依存せず、界面の存在も宣言しない。
使われ方：Π2-7′。旧二入力の置換と CLMST への付け替えは別工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (F : PerfectoidizationInterfaceE3 R p hR)
    (f : S →ₐ[R] T) (I : Ideal S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) →
        ∃! l : T →+* V, l.comp f.toRingHom = k)
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D}
    {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE)

include F hS hT hI harc in
/-- 指定普遍環だけから、元の四辺の引き戻しと差写像の全射性を得る。 -/
theorem perfectoidization_excision :
    let a := IsPerfectoidization.map hC hD f.toRingHom
    let b := IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)
    let c := IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))
    let d := IsPerfectoidization.map hQ hE
      (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map)
    IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b)
        (CommRingCat.ofHom c) (CommRingCat.ofHom d) ∧
      Function.Surjective (fun x : D × Q => c x.1 - d x.2) :=
  perfectoidization_excision_of_disc R S T p hR F f I hS hT hI harc
    (specified_disc p R hR F (ofAlgebra R S) ηS hC)
    (specified_disc p R hR F (ofAlgebra R T) ηT hD)
    (specified_disc p R hR F (quotientAlgebra R (ofAlgebra R S) I) ηQ hQ)
    (specified_disc p R hR F
      (quotientAlgebra R (ofAlgebra R T) (I.map f.toRingHom)) ηE hE) hC hD hQ hE

include F hS hT hI harc in
/-- 旧 excision 入力と同じ結論。追加引数は E3 界面のみである。 -/
theorem perfectoidization_excision_isPullback :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hC hD f.toRingHom))
      (CommRingCat.ofHom (IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)))
      (CommRingCat.ofHom (IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))))
      (CommRingCat.ofHom (IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map))) :=
  (perfectoidization_excision R S T p hR F f I hS hT hI harc hC hD hQ hE).1

include F hS hT hI harc hC in
/-- 同じ指定四辺の右辺 − 下辺は、加法的な差写像として全射である。 -/
theorem perfectoidization_excision_difference_surjective :
    Function.Surjective (fun x : D × Q =>
      IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom)) x.1 -
      IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map) x.2) :=
  (perfectoidization_excision R S T p hR F f I hS hT hI harc hC hD hQ hE).2

end SerrePositivity.BhattScholze.PerfectoidizationInterface
