/**
 * Law Telemetry Logger
 *
 * LDEにおける「観測による接地 (Grounding by Observation)」を実現するロガー。
 * 法則違反、ドメインイベント、システム状態を構造化された形式（JSON）で出力する。
 */

import { ErrorSeverity } from '../errors/definitions.js';

export interface LogContext {
  [key: string]: unknown;
}

export interface TelemetryEvent {
  event: string; // law.<domain>.<action>.<outcome>
  level: ErrorSeverity | 'debug';
  message: string;
  context?: LogContext;
  timestamp: string;
}

class LawLogger {
  private isJsonMode: boolean = false;

  constructor() {
    // 環境変数などでJSONモードを切り替える想定
    // デフォルトはfalseで人間可読形式
    this.isJsonMode = process.env.LOG_FORMAT === 'json';
  }

  public setJsonMode(enable: boolean) {
    this.isJsonMode = enable;
  }

  private emit(event: TelemetryEvent) {
    if (this.isJsonMode) {
      console.log(JSON.stringify(event));
    } else {
      const time = new Date(event.timestamp).toLocaleTimeString();
      const level = event.level.toUpperCase().padEnd(5);
      
      // 人間可読形式
      let output = `[${time}] ${level} [${event.event}] ${event.message}`;
      if (event.context && Object.keys(event.context).length > 0) {
         // コンテキストがある場合は整形して表示
         const contextStr = Object.entries(event.context)
           .map(([k, v]) => {
             const valStr = typeof v === 'object' ? JSON.stringify(v) : String(v);
             return `${k}=${valStr}`;
           })
           .join(' ');
         output += ` { ${contextStr} }`;
      }
      
      if (event.level === ErrorSeverity.Error) {
        console.error(output);
      } else {
        console.log(output);
      }
    }
  }

  public log(
    level: ErrorSeverity | 'debug',
    eventName: string,
    message: string,
    context?: LogContext
  ) {
    this.emit({
      event: eventName,
      level,
      message,
      context,
      timestamp: new Date().toISOString(),
    });
  }

  // Helper methods for specific levels
  public info(eventName: string, message: string, context?: LogContext) {
    this.log('info', eventName, message, context);
  }

  public warn(eventName: string, message: string, context?: LogContext) {
    this.log(ErrorSeverity.Warning, eventName, message, context);
  }

  public error(eventName: string, message: string, context?: LogContext) {
    this.log(ErrorSeverity.Error, eventName, message, context);
  }

  public debug(eventName: string, message: string, context?: LogContext) {
    this.log('debug', eventName, message, context);
  }

  /**
   * 法則違反の記録 (Law Violation Telemetry)
   * @param ruleId 違反した法則ID (ErrorCode)
   * @param message 詳細メッセージ
   * @param context 違反時のコンテキスト
   */
  public violation(ruleId: string, message: string, context?: LogContext) {
    this.log(
      ErrorSeverity.Error,
      `law.violation.${ruleId.toLowerCase()}`,
      message,
      { ruleId, ...context }
    );
  }
}

export const logger = new LawLogger();
