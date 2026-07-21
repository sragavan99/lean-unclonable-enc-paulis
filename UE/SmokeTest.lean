import UE.Examples.InterfaceDemo

/-! # Public API smoke test -/

#check UE.BitEncryptionFamily
#check UE.BitEncryptionFamily.PolynomiallyBoundedCipherDimension
#check UE.CloningAttack
#check UE.cloningSuccess
#check UE.SecureBitEncryption
#check UE.SecureBitEncryption.cipherDimension_polynomiallyBounded
#check UE.UncloneableBitExists

example : Prop := UE.UncloneableBitExists

example (S : UE.SecureBitEncryption) :
    S.encryption.PolynomiallyBoundedCipherDimension :=
  S.cipherDimension_polynomiallyBounded

example :
    UE.InterfaceDemo.candidateEncryption.PolynomiallyBoundedCipherDimension :=
  UE.InterfaceDemo.candidate_cipherDimension_polynomiallyBounded
