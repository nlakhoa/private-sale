
/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            
pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * ////IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}



/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * ////IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}




/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            
pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [////IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * ////IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}



/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            
pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}



/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            
pragma solidity ^0.8.0;

interface KeeperCompatibleInterface {
    /**
     * @notice method that is simulated by the keepers to see if any work actually
     * needs to be performed. This method does does not actually need to be
     * executable, and since it is only ever simulated it can consume lots of gas.
     * @dev To ensure that it is never called, you may want to add the
     * cannotExecute modifier from KeeperBase to your implementation of this
     * method.
     * @param checkData specified in the upkeep registration so it is always the
     * same for a registered upkeep. This can easily be broken down into specific
     * arguments using `abi.decode`, so multiple upkeeps can be registered on the
     * same contract and easily differentiated by the contract.
     * @return upkeepNeeded boolean to indicate whether the keeper should call
     * performUpkeep or not.
     * @return performData bytes that the keeper should call performUpkeep with, if
     * upkeep is needed. If you would like to encode data to decode later, try
     * `abi.encode`.
     */
    function checkUpkeep(bytes calldata checkData)
        external
        returns (bool upkeepNeeded, bytes memory performData);

    /**
     * @notice method that is actually executed by the keepers, via the registry.
     * The data returned by the checkUpkeep simulation will be passed into
     * this method to actually be executed.
     * @dev The input to this method should not be trusted, and the caller of the
     * method should not even be restricted to any single registry. Anyone should
     * be able call it, and the input should be validated, there is no guarantee
     * that the data passed in is the performData returned from checkUpkeep. This
     * could happen due to malicious keepers, racing keepers, or simply a state
     * change while the performUpkeep transaction is waiting for confirmation.
     * Always validate the data passed in.
     * @param performData is the data which was passed back from the checkData
     * simulation. If it is encoded, it can easily be decoded into other types by
     * calling `abi.decode`. This data should not be trusted, and should be
     * validated against the contract's current state.
     */
    function performUpkeep(bytes calldata performData) external;
}



/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            
pragma solidity ^0.8.0;

interface AggregatorV3Interface {
    function decimals() external view returns (uint8);

    function description() external view returns (string memory);

    function version() external view returns (uint256);

    // getRoundData and latestRoundData should both raise "No data present"
    // if they do not have data to report, instead of returning unset values
    // which could be misinterpreted as actual reported values.
    function getRoundData(uint80 _roundId)
        external
        view
        returns (
            uint80 roundId,
            int256 answer,
            uint256 startedAt,
            uint256 updatedAt,
            uint80 answeredInRound
        );

    function latestRoundData()
        external
        view
        returns (
            uint80 roundId,
            int256 answer,
            uint256 startedAt,
            uint256 updatedAt,
            uint80 answeredInRound
        );
}




/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            
////// SPDX-License-Identifier-FLATTEN-SUPPRESS-WARNING: MIT
// OpenZeppelin Contracts (last updated v4.6.0) (utils/math/SafeMath.sol)

pragma solidity ^0.8.0;

// CAUTION
// This version of SafeMath should only be used with Solidity 0.8 or later,
// because it relies on the compiler's built in overflow checks.

/**
 * @dev Wrappers over Solidity's arithmetic operations.
 *
 * NOTE: `SafeMath` is generally not needed starting with Solidity 0.8, since the compiler
 * now has built in overflow checking.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}



/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            
pragma solidity ^0.8.0;

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    enum Rounding {
        Down, // Toward negative infinity
        Up, // Toward infinity
        Zero // Toward zero
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds up instead
     * of rounding down.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }

    /**
     * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded down.
     *
     * Inspired by Henry S. Warren, Jr.'s "Hacker's Delight" (Chapter 11).
     */
    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of the target.
        //
        // We know that the "msb" (most significant bit) of our target number `a` is a power of 2 such that we have
        // `msb(a) <= a < 2*msb(a)`. This value can be written `msb(a)=2**k` with `k=log2(a)`.
        //
        // This can be rewritten `2**log2(a) <= a < 2**(log2(a) + 1)`
        // → `sqrt(2**k) <= sqrt(a) < sqrt(2**(k+1))`
        // → `2**(k/2) <= sqrt(a) < 2**((k+1)/2) <= 2**(k/2 + 1)`
        //
        // Consequently, `2**(log2(a) / 2)` is a good first approximation of `sqrt(a)` with at least 1 correct bit.
        uint256 result = 1 << (log2(a) >> 1);

        // At this point `result` is an estimation with one bit of precision. We know the true value is a uint128,
        // since it is the square root of a uint256. Newton's method converges quadratically (precision doubles at
        // every iteration). We thus need at most 7 iteration to turn our partial result with one bit of precision
        // into the expected uint128 result.
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            return min(result, a / result);
        }
    }

    /**
     * @notice Calculates sqrt(a), following the selected rounding direction.
     */
    function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = sqrt(a);
            return result + (rounding == Rounding.Up && result * result < a ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 2, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log2(value);
            return result + (rounding == Rounding.Up && 1 << result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 10, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10**64) {
                value /= 10**64;
                result += 64;
            }
            if (value >= 10**32) {
                value /= 10**32;
                result += 32;
            }
            if (value >= 10**16) {
                value /= 10**16;
                result += 16;
            }
            if (value >= 10**8) {
                value /= 10**8;
                result += 8;
            }
            if (value >= 10**4) {
                value /= 10**4;
                result += 4;
            }
            if (value >= 10**2) {
                value /= 10**2;
                result += 2;
            }
            if (value >= 10**1) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log10(value);
            return result + (rounding == Rounding.Up && 10**result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 256, rounded down, of a positive value.
     * Returns 0 if given 0.
     *
     * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
     */
    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 16;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 8;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 4;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 2;
            }
            if (value >> 8 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (rounding == Rounding.Up && 1 << (result * 8) < value ? 1 : 0);
        }
    }
}



/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            

pragma solidity ^0.8.0;


////import "./Address.sol";

////import "./IERC20.sol";
////import "./IERC20Permit.sol";
/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    function safePermit(
        IERC20Permit token,
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        uint256 nonceBefore = token.nonces(owner);
        token.permit(owner, spender, value, deadline, v, r, s);
        uint256 nonceAfter = token.nonces(owner);
        require(nonceAfter == nonceBefore + 1, "SafeERC20: permit did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}




/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/
            

pragma solidity ^0.8.0;

////import "./Context.sol";

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}


/** 
 *  SourceUnit: c:\Users\HP\Desktop\IBCO\hardhat-security-fcc\contracts\DakShowIbcoPrivateSale1.sol
*/

pragma solidity ^0.8.0;

////import "./lib/Ownable.sol";
////import "./lib/SafeERC20.sol";
////import "./lib/Math.sol";
////import "./lib/SafeMath.sol";
////import "./lib/AggregatorV3Interface.sol";
////import "./lib/KeeperCompatibleInterface.sol";

/*
 * @author Nguyen Le Anh Khoa
 * @notice Implement Initial Bonding Curve Offering for DakShow Token - Total 70M DAK token
 */

contract DakShowIbcoPrivateSale1 is Ownable, KeeperCompatibleInterface {
    using SafeERC20 for IERC20;

    AggregatorV3Interface internal priceFeedETH;
    AggregatorV3Interface internal priceFeedUSDT;
    AggregatorV3Interface internal priceFeedBNB;
    AggregatorV3Interface internal priceFeedBUSD;
    AggregatorV3Interface internal priceFeedUSDC;
    AggregatorV3Interface internal priceFeedBTC;

    event ClaimDAK(address indexed account, uint256 dakAmount);
    event DepositUSDT(address indexed account, uint256 amount);
    event DepositBUSD(address indexed account, uint256 amount);
    event DepositBNB(address indexed account, uint256 amount);
    event DepositUSDC(address indexed account, uint256 amount);
    event DepositBTC(address indexed account, uint256 amount);
    event DepositETH(address indexed account, uint256 amount);
    event PrivateSaleEND(bool status);

    // Contract types of tokens that can be used to deposit
    IERC20 public immutable dakshow;
    address payable public coldWallet;
    IERC20 internal usdt;
    IERC20 internal busd;
    IERC20 internal bnb;
    IERC20 internal usdc;
    IERC20 internal btc;

    uint256 public constant DECIMALS = 1e18;
    // DakShow Token has the same decimals as BNB (18)
    bool public end = false;

    // Status Private sale 1
    uint256 public afterEnd;
    // Total tokens that the user has deposited
    uint256 public totalUSDT = 0;
    uint256 public totalBUSD = 0;
    uint256 public totalBNB = 0;
    uint256 public totalUSDC = 0;
    uint256 public totalBTC = 0;
    uint256 public totalETH = 0;
    uint256 public totalDakIBCO = 0;
    uint256 public totalProvided = 0;

    // List of users who have joined
    address[] public userIBCO;

    // Total number of times that a user can withdraw tokens
    uint8 public totalClaim = 0;

    // Check user deposit
    mapping(address => bool) public deposited;

    // The amount of tokens that the user has deposited is converted to USD
    mapping(address => uint256) public provided;

    // Total amount of DAK tokens that the user can withdraw from the contract
    mapping(address => uint256) public totalDAKWithdraw;

    // Total number of DAK tokens that users can withdraw each time
    mapping(address => uint256) public balanceWithdraw;

    // Total amount of DAK tokens that the user withdrew from the contract
    mapping(address => uint256) public totalUserClaim;

    constructor(address payable _coldWallet, IERC20 _dak) {
        require(_coldWallet != address(0), "ColdWallet must be different from address(0)");
        coldWallet = _coldWallet;
        dakshow = _dak;
        usdt = IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);
        busd = IERC20(0x4Fabb145d64652a948d72533023f6E7A623C7C53);
        bnb = IERC20(0xB8c77482e45F1F44dE1745F52C74426C631bDD52);
        usdc = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
        btc = IERC20(0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599);

        priceFeedETH = AggregatorV3Interface(0x5f4eC3Df9cbd43714FE2740f5E3616155c5b8419);
        priceFeedUSDT = AggregatorV3Interface(0x3E7d1eAB13ad0104d2750B8863b489D65364e32D);
        priceFeedBNB = AggregatorV3Interface(0x14e613AC84a31f709eadbdF89C6CC390fDc9540A);
        priceFeedUSDC = AggregatorV3Interface(0x8fFfFfd4AfB6115b954Bd326cbe7B4BA576818f6);
        priceFeedBTC = AggregatorV3Interface(0xF4030086522a5bEEa4988F8cA5B36dbC97BeE88c);
        priceFeedBUSD = AggregatorV3Interface(0x833D8Eb16D306ed1FbB5D7A2E019e106B960965A);
    }

    // ---------- AUTOMATIC FUNCTION ----------

    function checkUpkeep(
        bytes calldata /*checkData*/
    )
        external
        view
        override
        returns (
            bool upkeepNeeded,
            bytes memory /* performData */
        )
    {
        upkeepNeeded = block.timestamp > afterEnd;
        return (upkeepNeeded, bytes(""));
    }

    function performUpkeep(
        bytes calldata /* performData*/
    ) external override {
        updateTotalWithdraw();
    }

    // Check token withdrawal time conditions
    modifier checkTimeUpdateWithdraw() {
        if (block.timestamp < afterEnd || totalClaim >= 11 || !end) {
            revert();
        }
        _;
    }

    // Increase the number of times a user can withdraw tokens
    function updateTotalWithdraw() public checkTimeUpdateWithdraw {
        afterEnd += 90 days;
        totalClaim++;
    }

    // Functions view the current price of tokens used in deposit
    function getLatestPriceETH() public view returns (int256) {
        (
            ,
            /*uint80 roundID*/
            int256 price, /*uint startedAt*/ /*uint timeStamp*/ /*uint80 answeredInRound*/
            ,
            ,

        ) = priceFeedETH.latestRoundData();
        return price;
    }

    function getLatestPriceUSDT() public view returns (int256) {
        (
            ,
            /*uint80 roundID*/
            int256 price, /*uint startedAt*/ /*uint timeStamp*/ /*uint80 answeredInRound*/
            ,
            ,

        ) = priceFeedUSDT.latestRoundData();
        return price;
    }

    function getLatestPriceBNB() public view returns (int256) {
        (
            ,
            /*uint80 roundID*/
            int256 price, /*uint startedAt*/ /*uint timeStamp*/ /*uint80 answeredInRound*/
            ,
            ,

        ) = priceFeedBNB.latestRoundData();
        return price;
    }

    function getLatestPriceBUSD() public view returns (int256) {
        (
            ,
            /*uint80 roundID*/
            int256 price, /*uint startedAt*/ /*uint timeStamp*/ /*uint80 answeredInRound*/
            ,
            ,

        ) = priceFeedBUSD.latestRoundData();
        return price;
    }

    function getLatestPriceUSDC() public view returns (int256) {
        (
            ,
            /*uint80 roundID*/
            int256 price, /*uint startedAt*/ /*uint timeStamp*/ /*uint80 answeredInRound*/
            ,
            ,

        ) = priceFeedUSDC.latestRoundData();
        return price;
    }

    function getLatestPriceBTC() public view returns (int256) {
        (
            ,
            /*uint80 roundID*/
            int256 price, /*uint startedAt*/ /*uint timeStamp*/ /*uint80 answeredInRound*/
            ,
            ,

        ) = priceFeedBTC.latestRoundData();
        return price;
    }

    /// @param amount Amount of USDT that user deposit
    function depositUSDT(uint256 amount) external {
        require(!end, "Private sale 1 has ended");

        int256 price = getLatestPriceUSDT();

        uint256 balanceDeposit = amount * uint256(price);

        uint256 dakWithdraw = getEstReceivedToken(balanceDeposit);

        require(
            70000000 * DECIMALS >= dakWithdraw + totalDakIBCO,
            "Insufficient DakShow token in contract"
        );

        require(usdt.balanceOf(msg.sender) >= amount, "Wallet address not enough tokens to pay");

        require(usdt.allowance(msg.sender, address(this)) >= amount, "Caller must approve first");

        if (!deposited[msg.sender]) {
            userIBCO.push(msg.sender);
            deposited[msg.sender] = true;
        }

        balanceWithdraw[msg.sender] += dakWithdraw / 12;

        provided[msg.sender] += balanceDeposit;

        totalUSDT += amount;

        totalDAKWithdraw[msg.sender] += (dakWithdraw * 11) / 12;

        totalDakIBCO += dakWithdraw;

        totalProvided += balanceDeposit;

        emit DepositUSDT(msg.sender, amount);

        SafeERC20.safeTransferFrom(usdt, msg.sender, coldWallet, amount);

        SafeERC20.safeTransfer(dakshow, msg.sender, dakWithdraw / 12);
    }

    /// @param amount Amount of BUSD that user deposit
    function depositBUSD(uint256 amount) external {
        int256 price = getLatestPriceBUSD();

        uint256 balanceDeposit = amount * uint256(price);

        uint256 dakWithdraw = getEstReceivedToken(balanceDeposit);

        require(!end, "Private sale 1 has ended");

        require(
            70000000 * DECIMALS >= dakWithdraw + totalDakIBCO,
            "Insufficient DakShow token in contract"
        );

        require(busd.balanceOf(msg.sender) >= amount, "Wallet address not enough tokens to pay");

        require(busd.allowance(msg.sender, address(this)) >= amount, "Caller must approve first");

        balanceWithdraw[msg.sender] += dakWithdraw / 12;

        provided[msg.sender] += balanceDeposit;

        totalBUSD += amount;

        totalDAKWithdraw[msg.sender] += (dakWithdraw * 11) / 12;

        totalDakIBCO += dakWithdraw;

        totalProvided += balanceDeposit;

        emit DepositBUSD(msg.sender, amount);

        SafeERC20.safeTransferFrom(busd, msg.sender, coldWallet, amount);

        SafeERC20.safeTransfer(dakshow, msg.sender, dakWithdraw / 12);
    }

    /// @param amount Amount of BNB that user deposit
    function depositBNB(uint256 amount) external {
        int256 price = getLatestPriceBNB();

        uint256 balanceDeposit = amount * uint256(price);

        uint256 dakWithdraw = getEstReceivedToken(balanceDeposit);

        require(!end, "Private sale 1 has ended");

        require(
            70000000 * DECIMALS >= dakWithdraw + totalDakIBCO,
            "Insufficient DakShow token in contract"
        );

        require(bnb.balanceOf(msg.sender) >= amount, "Wallet address not enough tokens to pay");

        require(bnb.allowance(msg.sender, address(this)) >= amount, "Caller must approve first");

        if (!deposited[msg.sender]) {
            userIBCO.push(msg.sender);
            deposited[msg.sender] = true;
        }

        balanceWithdraw[msg.sender] += dakWithdraw / 12;

        provided[msg.sender] += balanceDeposit;

        totalBNB += amount;

        totalDAKWithdraw[msg.sender] += (dakWithdraw * 11) / 12;

        totalDakIBCO += dakWithdraw;

        totalProvided += balanceDeposit;

        emit DepositBNB(msg.sender, amount);

        SafeERC20.safeTransferFrom(bnb, msg.sender, coldWallet, amount);

        SafeERC20.safeTransfer(dakshow, msg.sender, dakWithdraw / 12);
    }

    /// @param amount Amount of USDC that user deposit
    function depositUSDC(uint256 amount) external {
        int256 price = getLatestPriceUSDC();

        uint256 balanceDeposit = amount * uint256(price);

        uint256 dakWithdraw = getEstReceivedToken(balanceDeposit);

        require(!end, "Private sale 1 has ended");

        require(
            70000000 * DECIMALS >= dakWithdraw + totalDakIBCO,
            "Insufficient DakShow token in contract"
        );

        require(usdc.balanceOf(msg.sender) >= amount, "Wallet address not enough tokens to pay");

        require(usdc.allowance(msg.sender, address(this)) >= amount, "Caller must approve first");

        if (!deposited[msg.sender]) {
            userIBCO.push(msg.sender);
            deposited[msg.sender] = true;
        }

        balanceWithdraw[msg.sender] += dakWithdraw / 12;

        provided[msg.sender] += balanceDeposit;

        totalUSDC += amount;

        totalDAKWithdraw[msg.sender] += (dakWithdraw * 11) / 12;

        totalDakIBCO += dakWithdraw;

        totalProvided += balanceDeposit;

        emit DepositUSDC(msg.sender, amount);

        SafeERC20.safeTransferFrom(usdc, msg.sender, coldWallet, amount);

        SafeERC20.safeTransfer(dakshow, msg.sender, dakWithdraw / 12);
    }

    /// @param amount Amount of BTC that user deposit
    function depositBTC(uint256 amount) external {
        int256 price = getLatestPriceBTC();

        uint256 balanceDeposit = amount * uint256(price);

        uint256 dakWithdraw = getEstReceivedToken(balanceDeposit);

        require(!end, "Private sale 1 has ended");

        require(
            70000000 * DECIMALS >= dakWithdraw + totalDakIBCO,
            "Insufficient DakShow token in contract"
        );

        require(btc.balanceOf(msg.sender) >= amount, "Wallet address not enough tokens to pay");

        require(btc.allowance(msg.sender, address(this)) >= amount, "Caller must approve first");

        if (!deposited[msg.sender]) {
            userIBCO.push(msg.sender);
            deposited[msg.sender] = true;
        }

        balanceWithdraw[msg.sender] += dakWithdraw / 12;

        provided[msg.sender] += balanceDeposit;

        totalBTC += amount;

        totalDAKWithdraw[msg.sender] += (dakWithdraw * 11) / 12;

        totalDakIBCO += dakWithdraw;

        totalProvided += balanceDeposit;

        emit DepositBTC(msg.sender, amount);

        SafeERC20.safeTransferFrom(btc, msg.sender, coldWallet, amount);

        SafeERC20.safeTransfer(dakshow, msg.sender, dakWithdraw / 12);
    }

    /// @param amount Amount of ETH that user deposit
    function depositETH(uint256 amount) external payable {
        int256 price = getLatestPriceETH();

        uint256 balanceDeposit = amount * uint256(price);

        uint256 dakWithdraw = getEstReceivedToken(balanceDeposit);

        require(!end, "Private sale 1 has ended");

        require(
            70000000 * DECIMALS >= dakWithdraw + totalDakIBCO,
            "Insufficient DakShow token in contract"
        );

        require(msg.sender.balance >= amount, "Wallet address not enough tokens to pay");

        require(msg.value >= amount, "Insufficient amount of ether transferred");

        if (!deposited[msg.sender]) {
            userIBCO.push(msg.sender);
            deposited[msg.sender] = true;
        }

        balanceWithdraw[msg.sender] += dakWithdraw / 12;

        provided[msg.sender] += balanceDeposit;

        totalETH += amount;

        totalDAKWithdraw[msg.sender] += (dakWithdraw * 11) / 12;

        totalDakIBCO += dakWithdraw;

        totalProvided += balanceDeposit;

        emit DepositETH(msg.sender, amount);

        (bool sent, ) = coldWallet.call{value: amount}("");
        
        require(sent, "Failed to send Ether");

        SafeERC20.safeTransfer(dakshow, msg.sender, dakWithdraw / 12);
    }

    //  @return Returns total USD deposited in the contract of an address.
    function getUserDeposited(address _user) external view returns (uint256) {
        return provided[_user];
    }

    //  @return Returns total amount of DAK tokens that the user can withdraw from the contract.
    function getTokenDakWithdraw(address _user) external view returns (uint256) {
        return totalDAKWithdraw[_user];
    }

    //  @return Returns total number of DAK tokens that users can withdraw each time

    function getBalanceWithdraw(address userAddress) external view returns (uint256) {
        return balanceWithdraw[userAddress];
    }

    //  @return Returns the number of times the user has withdrawn DAK tokens from the contract

    function getTotalUserClaim(address userAddress) external view returns (uint256) {
        return totalUserClaim[userAddress];
    }

    /**
     * @dev Get estimated DakShow token price
     */
    function getEstTokenPrice() public view returns (uint256) {
        return (2403 * totalDakIBCO * 10**5) / DECIMALS + (57 * DECIMALS) / 20000;
    }

    /**
     * @return Calculate the amount of DAK tokens that the user will receive based on the amount of USD that the user provides
     */
    function getEstReceivedToken(uint256 amount) public view returns (uint256) {
        uint256 params = (1335 * amount) / 10**22 + (1335 * totalProvided) / 10**14 + 225625000000;
        return ((20000000 * Math.sqrt(params)) / 8010 - 1186017480) * 10**16 - totalDakIBCO;
    }

    // Calculate the remaining amount of DAK tokens equivalent to how much USD
    function quantityRemaining() public view returns (uint256) {
        return
            788235 *
            DECIMALS -
            ((2403 * ((totalDakIBCO / DECIMALS)**2) * 10**5) /
                2 +
                (285 * 10**13 * totalDakIBCO) /
                DECIMALS);
    }

    // @notice  User can buy all remaining DAK tokens with BUSD by calling this function
    function buyRemainingQuantity() external {
        uint256 amount = quantityRemaining();

        uint256 currentDakRemaining = dakshow.balanceOf(address(this));

        require(!end, "Private sale 1 has ended");

        require(busd.balanceOf(msg.sender) >= amount, "Wallet address not enough tokens to pay");

        require(busd.allowance(msg.sender, address(this)) >= amount, "Caller must approve first");

        if (!deposited[msg.sender]) {
            userIBCO.push(msg.sender);
            deposited[msg.sender] = true;
        }

        balanceWithdraw[msg.sender] += currentDakRemaining / 12;

        end = true;

        afterEnd = block.timestamp;

        provided[msg.sender] += amount;

        totalBUSD += amount;

        totalDAKWithdraw[msg.sender] += (currentDakRemaining * 11) / 12;

        totalDakIBCO += currentDakRemaining;

        totalProvided += amount;

        emit DepositBUSD(msg.sender, amount);

        emit PrivateSaleEND(true);

        SafeERC20.safeTransferFrom(busd, msg.sender, coldWallet, amount);

        SafeERC20.safeTransfer(dakshow, msg.sender, currentDakRemaining / 12);
    }

    // @param addressReward The address where the user wants to transfer the DAK token they own
    function claimToken(address addressReward) external {
        uint256 amount = balanceWithdraw[msg.sender] * (totalClaim - totalUserClaim[msg.sender]);

        require(totalDAKWithdraw[msg.sender] > 0, "Address does not have enough dak to withdraw");

        require(dakshow.balanceOf(address(this)) >= amount, "Not enough tokens to transfer");

        require(totalClaim > totalUserClaim[msg.sender], "Not enough time to withdraw");

        totalUserClaim[msg.sender] = totalClaim;

        totalDAKWithdraw[msg.sender] -= amount;

        emit ClaimDAK(msg.sender, amount);

        SafeERC20.safeTransfer(dakshow, addressReward, amount);
    }

    receive() external payable {}

    // Fallback function is called when msg.data is not empty
    fallback() external payable {}
}

